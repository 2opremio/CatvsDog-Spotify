// Copyright © 2013 Alfonso Acosta <alfonso.acosta@gmail.com>.
// All Rights Reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
//     1. Redistributions of source code must retain the above
//     copyright notice, this list of conditions and the following
//     disclaimer.
//
//     2. Redistributions in binary form must reproduce the above
//     copyright notice, this list of conditions and the following
//     disclaimer in the documentation and/or other materials provided
//     with the distribution.
//
//     3. The name of the author may not be used to endorse or promote
//     products derived from this software without specific prior
//     written permission.
//
//     THIS SOFTWARE IS PROVIDED "AS IS" AND ANY EXPRESS OR IMPLIED
//     WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
//     WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
//     PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE
//     FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
//     CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
//     PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
//     OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
//     THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
//     TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
//     OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY
//     OF SUCH DAMAGE.

#include <climits>
#include <cstdlib>
#include <map>
#include <vector>
#include <queue>
#include <string>
#include <sstream>
#include <iostream>

using namespace std;

/////////////////////////////////
// DESCRIPTION OF THE SOLUTION //
/////////////////////////////////

// This program solves the Cat vs. Dog Tech Puzzle,
// as formulated in Spotify's web-site [1]
//
// Solving the Cat vs. Dog problem boils down to finding the
// maximum-weighted independent set [2] of a bipartite graph [3].
//
// The steps followed to solve the problem are:
//
// 1. Build a undirected, vertex-weighted, bipartite graph,
//    G(C union D, E, w), where:
//
//   1.1 C and D are the two disjoint sets of vertices of the graph.
//       Vertices model votes as follows:
//       * C are the votes "to keep cats" (i.e. votes of the type "Cx Dy")
//       * D are the votes "to keep dogs" (i.e. votes of the type "Dx Cy")
//
//   1.2 w is the vertex weight function, w : (D union C) -> |N. We
//       define it as the "vote count" of each vote (i.e. w(v) gives us
//       how many times v appears in the problem description).
//
//   1.3 E are the edges connecting D and C. We build E so that it
//       connects incompatible vertices (incompatible votes).
//       Two votes are incompatible if they cannot be satisfied
//       simultaneously.  More formally, vote "Cx1 Dy1" is incompatible
//       with vote "Dx2 Cy2" if:

//          x1 equals y2
//          or
//          x2 equals y1
//
//       For instance, votes "D11 C40" and "C13 D11", are
//       incompatible. So are "C7 D5" and "D23 C7".
//
//   Note that G is guaranteed to be bipartite by construction since,
//   due to "the universal fact that everyone is either a cat lover
//   (i.e. a dog hater) or a dog lover (i.e. a cat hater), it has been
//   decided that each vote must name exactly one cat and exactly one
//   dog." [1]
//
// 2. Find M, the maximum-weighted independent set [2] of G.
//
//    The "maximum number of viewers" [1] (let's call it MAX_VIEWERS)
//    is the sum of the weighs of all the vertices (votes) in M
//    (i.e. MAX_VIEWERS = sum(w(v)) for every v in M).
//
//    For a general graph, finding M is known to be an NP-hard [4] problem,
//    just like finding the maximum-cardinality independent set
//    (i.e. finding M when the graph has an identical weigh for all
//    vertices).
//
//    However, in the case of bipartite graphs, polynomial-time
//    algorithms exist. The approach taken by this program is to
//    transform G into a Flow Network [5] and compute its maximum flow
//    (MAX_FLOW from now on).
//
//    In order to transform G to a flow network (FN) the following
//    steps are taken:
//
//    2.1. Add two new vertices s and t, not present in G:
//         * s (source)
//         * t (sink)
//
//    2.2 Connect s to all the votes in C. For every c in C,
//        capacity(s,c) = w(c)
//
//    2.3 Connect all the votes in D with t. For every d in D,
//        capacity(d,t) = w(d)
//
//    2.4 Maintain all the edges already present between C and D and
//        assign them an infinite capacity. That is, for every (x,y) in E
//        capacity(x,y) = infinite.
//
//    Then, we must compute the maximum flow of FN (MAX_FLOW).
//
//    Finally, MAX_VIEWERS = TOTAL_VOTES - MAX_FLOW.
//
//    Where TOTAL_VOTES is the total number of votes, more formally,
//    TOTAL_VOTES = sum(v) for every v in (C union D)
//
//    Note that, when building the Flow Network, C and D are interchangeable
//    (we could have used C instead of D and C instead of D for steps 2.2 and
//     2.3)
//
// [1] https://www.spotify.com/mc/jobs/tech/catvsdog/ (checked in march 5 2013)
// [2] http://en.wikipedia.org/wiki/Independent_set_(graph_theory)
// [3] http://en.wikipedia.org/wiki/Bipartite_graph
// [4] http://en.wikipedia.org/wiki/NP-hard
// [5] http://en.wikipedia.org/wiki/Flow_network


//////////////////////////
// IMPLEMENTATION NOTES //
//////////////////////////

// * Since I wasn't sure about how Spotify's corrector would behave
//   with multiple files, I decided to include all the code in one
//   file.  Admittedly, this hurts readability (trust me, it also made
//   it more difficult to write). But, as a nice side-effect, it also
//   improves performance since the compiler can potentially inline
//   all the methods.
//
// * Pet identifiers are translated to a canonical representation
//   (minimum identifiers possible) during parsing, allowing to store votes
//   in matrices with minimum size.
//
// * I use a functor-based, overly protective line parser. A bit
//   overkill for such a small problem, but I couldn't help it.
//
// * The algorithm chosen to compute the maximum flow is
//   Ford–Fulkerson [1] using breadth-first search to obtain the
//   paths to the sink (also known as Edmonds–Karp [2]). Its time-complexity
//   is O(|D union C|^2 * |E|) (notation: Given a set S, |S| denotes its cardinality).
//
//   A recent publication claims to provide a linear-time algorithm [3] but
//   I didn't look deeply into it.
//
// * The computation of the incompatibilities has a complexity
//   of O(|D| * |C| * (|D|+|C|))
//
// * I purposely decided to represent E in a map pairing votes with
//   their edges. This implies that obtaining the edges of a vote has
//   a time-complexity of log(|D| + |C|) as opposed to O(1) if I
//   packed the edges directly with each vote. However, this decouples
//   the flow network from the original votes, leading to a cleaner
//   design.
//
//   This would actually be the first performance improvement I would
//   consider.
//
// [1] http://en.wikipedia.org/wiki/Ford%E2%80%93Fulkerson_algorithm
// [2] http://en.wikipedia.org/wiki/Edmonds%E2%80%93Karp_algorithm
// [3] http://jorlin.scripts.mit.edu/Max_flows_in_O(nm)_time.html

////////////////
// BASIC TYPES//
////////////////

// The number of appearances of a specific vote
typedef unsigned int vote_count_t;

// The identifier of a pet (cat or dog), starting at 1
typedef unsigned int pet_identifier_t;

//////////
// VOTE //
//////////

struct VoteId
{
  typedef enum{KEEP_DOG, KEEP_CAT} Kind;
  const Kind kind;
  const pet_identifier_t pet_to_keep;
  const pet_identifier_t pet_to_throw_out;
  VoteId(const Kind &kind,
         const pet_identifier_t &pet_to_keep,
         const pet_identifier_t &pet_to_throw_out):
      kind(kind), pet_to_keep(pet_to_keep), pet_to_throw_out(pet_to_throw_out) {}
};


struct Vote
{
  const VoteId id;
  vote_count_t count;
  Vote(const VoteId &id): id(id), count(1){}
};

/////////////////////////////////////////////////
// VOTES TO KEEP ONE KIND OF PET (DOGS or CATS)//
////////////////////////////////////////////////

// All the "keep" votes for one kind of pet e.g all the votes issued
// to keep dogs, for instance "D23 C 40"
struct KeepVotesForPetKind
{
 private:
  Vote **votes;

  // internal verson of get vote pointer which returns a
  // reference instead of a copy
  inline Vote* &unsafeGetVote_p(const pet_identifier_t &this_kind_id,
                                const pet_identifier_t &other_kind_id)
      const
  {
    return *(votes + other_kind_id * thiskind_petnum + this_kind_id);
  }

 public:

  const pet_identifier_t thiskind_petnum;
  const pet_identifier_t oppositekind_petnum;

  KeepVotesForPetKind(unsigned int thiskind_petnum,
                      unsigned int oppositekind_petnum):
      thiskind_petnum(thiskind_petnum),
      oppositekind_petnum(oppositekind_petnum)
  {
    // I use malloc and free on purpose so that
    // we don't get any kind of initialization overhead
    // the real initialization will happen at parsing time
    votes = (Vote**) calloc(thiskind_petnum,
                            oppositekind_petnum * sizeof(Vote*));
  }

  virtual ~KeepVotesForPetKind()
  {
    pet_identifier_t i, j;
    for(i = 0; i < thiskind_petnum; i++)
      for(j = 0; j < oppositekind_petnum; j++)
      {
        Vote* &vote_p = unsafeGetVote_p(i, j);
        if(vote_p != 0)
          delete vote_p;
      }
    free(votes);
    votes = NULL;
  }

  // If NULL, the vote does not exist. There is no bound-checking
  // for pets out of the problem specification.
  inline Vote *getVote_p(const pet_identifier_t& this_kind_id,
                         const pet_identifier_t& other_kind_id)
      const
  {
    return unsafeGetVote_p(this_kind_id, other_kind_id);
  }

  void insertVote(pet_identifier_t this_kind_id,
                  pet_identifier_t other_kind_id,
                  VoteId id)
  {
    Vote* & vote_p = unsafeGetVote_p(this_kind_id, other_kind_id);
    if(vote_p == 0)
    {
      vote_p = new Vote(id);
    }
    else
    {
      vote_p->count++;
    }
  }
};


//////////////////////
// VOTES ALTOGETHER //
//////////////////////

typedef KeepVotesForPetKind KeepVotesForCats;
typedef KeepVotesForPetKind KeepVotesForDogs;

// Contains all the votes provided in a problem instance
struct Votes
{
  static const pet_identifier_t max_dogs_cardinality = 100;
  static const pet_identifier_t max_cats_cardinality = 100;
  const vote_count_t total_votes;
  KeepVotesForCats for_cats;
  KeepVotesForCats for_dogs;

  Votes(vote_count_t total_votes,
        pet_identifier_t cat_number,
        pet_identifier_t dog_number):
      total_votes(total_votes),
      for_cats(cat_number, dog_number),
      for_dogs(dog_number, cat_number)
  {}
};


//////////////////
// FLOW NETWORK //
//////////////////

// Adapter class around Votes to provide a flow network as described
// in the Description of the Solution.
class FlowNetwork
{
 private:
  Votes &votes;
  Vote source;
  Vote sink;

  // The flow can be negative for inverse edges during the
  // maximum flow search
  typedef int flow_t;
  typedef vote_count_t capacity_t;
  static const capacity_t infinite_capacity = UINT_MAX;

  struct FlowEdge
  {
    FlowEdge *inverse_edge;
    Vote *destination;
    capacity_t capacity;
    flow_t flow;
  };

  class FlowEdges
  {
   private:
    Votes &votes;
    Vote  &source;
    Vote  &sink;
    typedef vector<FlowEdge*> FlowEdgesVector;
    // Table containing the edges (incompatibilities) of each vote
    //
    // Again, we could keep the full vote identifier as a key
    // but since votes are not duplicated this is equivalent and
    // much faster
    //
    // Additionally , as mentioned in the implementation notes
    // it would be much faster (O(1) vs O(log(n))
    // to simply include the edges directly in each Vote but it
    // is dirtier since it couples the votes with the flow network.
    typedef  map<Vote*, FlowEdgesVector> VoteFlowEdgesTable;
    VoteFlowEdgesTable vote_flowedges_table;
    // Keep track of allocated edges in order to delete them
    FlowEdgesVector flow_edges_to_delete;

    inline void allocateFlowEdgePair(Vote *origin,
                                     Vote *destination,
                                     capacity_t direct_edge_capacity,
                                     FlowEdge* &direct_edge_out,
                                     FlowEdge* &inverse_edge_out)
    {
      direct_edge_out = new FlowEdge;
      inverse_edge_out = new FlowEdge;
      direct_edge_out->capacity = direct_edge_capacity;
      inverse_edge_out->capacity = 0;
      direct_edge_out->flow = 0;
      inverse_edge_out->flow = 0;
      direct_edge_out->destination = destination;
      inverse_edge_out->destination = origin;
      direct_edge_out->inverse_edge = inverse_edge_out;
      inverse_edge_out->inverse_edge = direct_edge_out;
      flow_edges_to_delete.push_back(direct_edge_out);
      flow_edges_to_delete.push_back(inverse_edge_out);
    }

   public:

    FlowEdges(Votes &votes, Vote &source, Vote &sink):
        votes(votes), source(source), sink(sink)
    {
      // Resolve the edges (i.e. vote incompatibilities)
      //
      // Edges are generated preventively, and cached in
      // vote_flow_edges_table.
      //
      // The flow network edges are connected as follows:
      //
      // source (1)-> votes_to_keep_cats (2)-> votes_to_keep_dogs (3)-> sink
      //
      // 1. The source is connected to every "vote to keep cat", with
      //    a capacity of vote_count (the number of repetitions of the
      //    vote)
      //
      // 2. Votes for cats and votes for dogs are connected according
      //    to their incompatibilities. Vote (keep cati, throw dogj)
      //    is incompatible with vote (keep dogx, throw caty) in which
      //    i equals y or j equals x.  For these edges, capacities are
      //    initially set to infinite.
      //
      // 3. The sink is connected to every "vote to keep dog" using,
      //    again, a capacity of vote_count.
      //
      // 4. Additionaly as Edmonds–Karp mandates, for every edge, we
      //    also include an inverted edge with capacity of 0.
      //
      // Note: the reverse order would had also been valid

      pet_identifier_t cat_id, dog_id;
      FlowEdge *direct_edge;
      FlowEdge *inverse_edge;

      // Note: a naive, quadratic traversal would had looked much nicer
      //       but much less efficient than all these nested loops

      // 1. Add edges:
      //  a. between source and "votes to keep cats"
      //  b. between "votes to keep cats" and "votes to keep dogs"
      Vote* to_keep_cat_vote_p;
      FlowEdgesVector &source_edges = vote_flowedges_table[&source];
      pet_identifier_t incompatible_cat_id, incompatible_dog_id;
      Vote* incompatible_vote_p;

      for(cat_id = 0; cat_id < votes.for_cats.thiskind_petnum; cat_id++)
        for(dog_id = 0; dog_id < votes.for_cats.oppositekind_petnum; dog_id++)
        {
          to_keep_cat_vote_p = votes.for_cats.getVote_p(cat_id, dog_id);
          if(to_keep_cat_vote_p == 0)
            continue;
          FlowEdgesVector &to_keep_cat_vote_edges = vote_flowedges_table[to_keep_cat_vote_p];
          // a. between source and "votes to keep cats"
          allocateFlowEdgePair(&source,
                               to_keep_cat_vote_p,
                               to_keep_cat_vote_p->count,
                               direct_edge,
                               inverse_edge);
          source_edges.push_back(direct_edge);
          to_keep_cat_vote_edges.push_back(inverse_edge);

          // b. between "votes to keep cats" and "votes to keep dogs"
          // Firstly, let's add edges for the incompatibilities with dog_id
          for(incompatible_cat_id = 0;
              incompatible_cat_id < votes.for_dogs.oppositekind_petnum;
              incompatible_cat_id++)
          {
            incompatible_vote_p = votes.for_dogs.getVote_p(dog_id, incompatible_cat_id);
            if(incompatible_vote_p == 0)
              continue;
            allocateFlowEdgePair(to_keep_cat_vote_p,
                                   incompatible_vote_p,
                                   infinite_capacity,
                                   direct_edge,
                                   inverse_edge);
            to_keep_cat_vote_edges.push_back(direct_edge);
            vote_flowedges_table[incompatible_vote_p].push_back(inverse_edge);
          }

          // Lastly, let's add edges for the incompatibilities with cat_id
          for(incompatible_dog_id = 0;
              incompatible_dog_id < dog_id;
              incompatible_dog_id++)
          {
            incompatible_vote_p = votes.for_dogs.getVote_p(incompatible_dog_id, cat_id);
            if(incompatible_vote_p == 0)
              continue;
            allocateFlowEdgePair(to_keep_cat_vote_p,
                                   incompatible_vote_p,
                                   infinite_capacity,
                                   direct_edge,
                                   inverse_edge);
            to_keep_cat_vote_edges.push_back(direct_edge);
            vote_flowedges_table[incompatible_vote_p].push_back(inverse_edge);
          }
          // Split it in two to avoid adding the inverse vote twice
          // (e.g. C1D1 and D1C1)
          for(incompatible_dog_id = dog_id+1;
              incompatible_dog_id < votes.for_dogs.thiskind_petnum;
              incompatible_dog_id++)
          {
            incompatible_vote_p = votes.for_dogs.getVote_p(incompatible_dog_id, cat_id);
            if(incompatible_vote_p == 0)
              continue;
            allocateFlowEdgePair(to_keep_cat_vote_p,
                                   incompatible_vote_p,
                                   infinite_capacity,
                                   direct_edge,
                                   inverse_edge);
            to_keep_cat_vote_edges.push_back(direct_edge);
            vote_flowedges_table[incompatible_vote_p].push_back(inverse_edge);

          }
        }

      // Add edges between the "votes to keep dogs" and the sink
      FlowEdgesVector &sink_edges = vote_flowedges_table[&sink];
      Vote* to_keep_dog_vote_p;
      for(dog_id = 0; dog_id < votes.for_dogs.thiskind_petnum; dog_id++)
        for(cat_id = 0; cat_id < votes.for_dogs.oppositekind_petnum; cat_id++)
        {
          to_keep_dog_vote_p = votes.for_dogs.getVote_p(dog_id, cat_id);
          if(to_keep_dog_vote_p == 0)
            continue;
          allocateFlowEdgePair(to_keep_dog_vote_p,
                                 &sink,
                                 to_keep_dog_vote_p->count,
                                 direct_edge,
                                 inverse_edge);
          vote_flowedges_table[to_keep_dog_vote_p].push_back(direct_edge);
          sink_edges.push_back(inverse_edge);
        }

    }

    ~FlowEdges()
    {
      FlowEdgesVector::iterator it;
      for(it = flow_edges_to_delete.begin();
          it != flow_edges_to_delete.end();
          it++)
        delete *it;
    }

    // Get the edges to which "vote" is connected
    vector<FlowEdge*>& getVoteEdges(Vote *const vote)
    {
      return vote_flowedges_table[vote];
    }
  };

  // Efficient structures for Breadth-first search

  // This data structures are a "mix" between a linked list (to
  // find the edges of a path) and a table (to find the path until
  // certain vote in log time)

  // The path from the source until certain node
  struct BfsPath
  {
    // Avialable Capacity found until the end of this path
    capacity_t found_capacity;
    BfsPath *path_prefix;
    FlowEdge* const last_edge;
    BfsPath(capacity_t found_capacity, BfsPath *path_prefix, FlowEdge* last_edge):
        found_capacity(found_capacity),
        path_prefix(path_prefix),
        last_edge(last_edge)
    {}
  };

  // Paring of votes and paths. For vote v, it provides the path until v.
  // We could use full VotesIds as a keys, but there are no vote duplicates
  // (i.e. pointers are unique) so comparing pointers is equivalent and
  // much faster.
  typedef map<Vote*, BfsPath> BfsPaths;

  // Find a path from source to sink with available capacity > 0
  // If 0 is returned, no path was found
  BfsPath* breadthFirstSearch(BfsPaths &paths, FlowEdges &edges)
  {
    // Initialization of paths
    paths.clear();
    static BfsPath source_path(infinite_capacity, 0, 0);
    BfsPaths::value_type source_entry(&source, source_path);
    paths.insert(source_entry);

    // Allocate the queue
    queue<BfsPaths::value_type*> q;
    q.push(&source_entry);

    while(!q.empty())
    {
      // Obtain vote u and its path
      BfsPaths::value_type *path_to_u = q.front();
      q.pop();

      // Iterate over all edges reached by u
      vector<FlowEdge*> &u_edges = edges.getVoteEdges((*path_to_u).first);

      for(vector<FlowEdge*>::iterator it = u_edges.begin(); it != u_edges.end(); it++)
      {
        FlowEdge &edge = **it;

        // Check if the edge has available capacity
        capacity_t available_capacity = edge.capacity - edge.flow;
        if(available_capacity > 0)
        {
          Vote *v = edge.destination;

          // Check if v was visited and insert it in the paths if it wasn't
          // We do it by preventively trying to insert it
          // and then checking the result.
          capacity_t found_capacity = min((*path_to_u).second.found_capacity,
                                          available_capacity);
          BfsPaths::value_type path_to_v(v,
                                         BfsPath(found_capacity,
                                                 &(*path_to_u).second,
                                                 &edge));
          pair<BfsPaths::iterator,bool> insert_result = paths.insert(path_to_v);

          if(v == &sink)
          {
            // :) wooohoooo, we found our path!
            return &(*insert_result.first).second;
          }
          else if(insert_result.second)
          {
            // if the vote wasn't visited yet, push it in the queue
            // otherwise don't bother
            q.push(&*insert_result.first);
          }

        }
      }
    }

    // No path was found
    return 0;
  }

 public:

  FlowNetwork(Votes &votes):
      votes(votes),
      // Pick the source and the sink votes so that they cannot be present
      // in any problem instance
      source(VoteId(VoteId::KEEP_CAT, UINT_MAX, UINT_MAX)),
      sink(VoteId(VoteId::KEEP_DOG, UINT_MAX, UINT_MAX))
  {}

  // Obtain the maximum flow of the network using Ford–Fulkerson
  // with breadth-first search to find the paths to the sink
  // (Edmonds–Karp algorithm)
  vote_count_t getMaximumFlow()
  {
    flow_t maximum_flow = 0;
    BfsPaths paths;
    FlowEdges edges(votes, source, sink);

    BfsPath *bfs_result;
    while(bfs_result = breadthFirstSearch(paths, edges), bfs_result != 0)
    {
      capacity_t found_capacity = bfs_result->found_capacity;
      maximum_flow += found_capacity;

      for(BfsPath *path_prefix = bfs_result;
          path_prefix->last_edge != 0;
          path_prefix = path_prefix->path_prefix)
      {
        path_prefix->last_edge->flow += found_capacity;
        path_prefix->last_edge->inverse_edge->flow -= found_capacity;
      }
    }
    return maximum_flow;
  }
};


/////////////
// PARSING //
/////////////

// To allow debugging with spotify's automatic corrector
// (when failing it only provides an error code, well
//  that's better than nothing!)
typedef int ParseErrorCode;
#define NO_ERROR                                0
#define VOTE_SYNTAX_ERROR                       1
#define UNEXPECTED_THROW_OUT_PREFIX_IN_CAT_VOTE 2
#define UNEXPECTED_THROW_OUT_PREFIX_IN_DOG_VOTE 3
#define UNKNOWN_VOTE_KIND                       4
#define MORE_PETS_THAN_SPECIFIED                5
#define PROBLEM_SPEC_SYNTAX_ERROR               6
#define SPEC_SURPASES_BOUNDARIES                7
#define PROBLEM_INSTANCE_NUM_SYNTAX_ERROR       8
#define CANNOT_READ_LINE                        9
#define MORE_PETS_THAN_SPECIFIED_POST_PARSE    10

// Thrown when an error was found during parsing
class ParsingException
{
 public:
  ParsingException(unsigned int line_number,
                   string error_description,
                   ParseErrorCode error_code):
      line_number(line_number),
      error_description(error_description),
      error_code(error_code)
  {};

  unsigned int lineNumber() {return line_number;};
  string &getErrorDescription() {return error_description;};
  ParseErrorCode getParseErrorCode() {return error_code;};

 private:
  unsigned int line_number;
  string error_description;
  ParseErrorCode error_code;
};

// Functor-based parser.
// Parses lines from an input stream according to parsers
// provided by the user.
class LineParser
{
 private:
  istream &input_stream;
  istringstream line_stream;
  string line;
  unsigned int current_line_number;
 public:

  // Parser used to parse each line
  class Parser
  {
   public:
    virtual pair<string,ParseErrorCode> getSyntaxError() = 0;
    virtual void parse(istream &input_stream) = 0;
    virtual pair<string,ParseErrorCode> checkSemantics() = 0;
    virtual ~Parser(){}
  };

  // Build a Line parser from an input stream
  // and indicate what number to use for the first
  // line parsed
  LineParser(istream &input_stream,
             unsigned int first_line_number):
      input_stream(input_stream),
      current_line_number(first_line_number)
  {}

  unsigned int getCurrentLineNumber()
  {
    return current_line_number;
  }

  // Applies the provided parser to the next line
  // from the input stream
  void parseLine(Parser &parser)
  {
    line.clear();
    if(std::getline(input_stream, line).fail())
      throw(ParsingException(current_line_number,
                             "cannot read line",
                             CANNOT_READ_LINE));
    line_stream.clear();
    line_stream.str(line);
    parser.parse(line_stream);
    if(line_stream.fail())
    {
      pair<string,ParseErrorCode> syntax_error_cause =
          parser.getSyntaxError();
      throw(ParsingException(current_line_number,
                             syntax_error_cause.first + ": '" + line + "'",
                             syntax_error_cause.second));
    }
    pair<string,ParseErrorCode> semantic_error_cause =
        parser.checkSemantics();
    if(semantic_error_cause.second != NO_ERROR)
    {
      throw(ParsingException(current_line_number,
                             semantic_error_cause.first + ": '" + line + "'",
                             semantic_error_cause.second));
    }
    current_line_number++;
  }
};

// Helper object to trim input strings (i.e. remove blanks)
struct Trimmer{} trim;
istream & operator>>(istream &in, Trimmer &)
{
    while(isspace(in.peek()))
    {
      in.get();
    }
    return in;
}

// Translate pet ids to cannonical form to insert them
// easily in a minimum-sized matrix
typedef map<pet_identifier_t,pet_identifier_t> PetIdTranslationTbl;

static inline pet_identifier_t translatePetId(pet_identifier_t original_pet_id,
                                              pet_identifier_t &next_avialable_pet_id,
                                              PetIdTranslationTbl &translation_tbl)
{
  pet_identifier_t canonical_pet_id;
  // Assume that the id wasn't canonical yet
  // and react based on the result
  PetIdTranslationTbl::value_type to_insert(original_pet_id,
                                            next_avialable_pet_id);
  pair<PetIdTranslationTbl::iterator, bool> insert_result =
      translation_tbl.insert(to_insert);
  if(insert_result.second)
  {
    // First time we are translating this id
    canonical_pet_id = next_avialable_pet_id++;
  }
  else
  {
    // Id which was already assigned a translation
    canonical_pet_id = (*(insert_result.first)).second;
  }
  return canonical_pet_id;
}

// Parses a vote line and translates the vote to canonical
// representation
class VoteParser: public LineParser::Parser
{
 private:
  // Parsing per-se
  static const char dog_prefix = 'D';
  static const char cat_prefix = 'C';
  char pet_to_keep_prefix, pet_to_throw_out_prefix;
  pet_identifier_t &pet_to_keep, &pet_to_throw_out;
  VoteId::Kind &vote_kind;

  // Translation to canonical form
  pet_identifier_t &canonical_cat_id, &canonical_dog_id;
  pet_identifier_t &next_available_cat_id, &next_available_dog_id;
  PetIdTranslationTbl &cat_translation_tbl, &dog_translation_tbl;

  // Global parameters (total number of cats and dogs)
  const pet_identifier_t &cat_number, &dog_number;

 public:
  VoteParser(pet_identifier_t &pet_to_keep,
             pet_identifier_t &pet_to_throw_out,
             VoteId::Kind &vote_kind,
             pet_identifier_t &canonical_cat_id,
             pet_identifier_t &canonical_dog_id,
             pet_identifier_t &next_available_cat_id,
             pet_identifier_t &next_available_dog_id,
             PetIdTranslationTbl &cat_translation_tbl,
             PetIdTranslationTbl &dog_translation_tbl,
             const pet_identifier_t &cat_number,
             const pet_identifier_t &dog_number):
      pet_to_keep(pet_to_keep),
      pet_to_throw_out(pet_to_throw_out),
      vote_kind(vote_kind),
      canonical_cat_id(canonical_cat_id),
      canonical_dog_id(canonical_dog_id),
      next_available_cat_id(next_available_cat_id),
      next_available_dog_id(next_available_dog_id),
      cat_translation_tbl(cat_translation_tbl),
      dog_translation_tbl(dog_translation_tbl),
      cat_number(cat_number),
      dog_number(dog_number)
  {}

  pair<string,ParseErrorCode> getSyntaxError()
  {
    return pair<string,ParseErrorCode>("vote syntax error", VOTE_SYNTAX_ERROR);
  }

  void parse(istream &in)
  {
    // vote prefixes
    in >> trim;
    in.get(pet_to_keep_prefix) >> pet_to_keep >> trim;
    in.get(pet_to_throw_out_prefix) >> pet_to_throw_out;
  }

  pair<string,ParseErrorCode> checkSemantics()
  {
    pair<string,ParseErrorCode> error_cause("", NO_ERROR);

    switch(pet_to_keep_prefix)
    {
      case cat_prefix:
        vote_kind = VoteId::KEEP_CAT;
        canonical_cat_id = translatePetId(pet_to_keep,
                                           next_available_cat_id,
                                           cat_translation_tbl);
        canonical_dog_id = translatePetId(pet_to_throw_out,
                                           next_available_dog_id,
                                           dog_translation_tbl);

        if(pet_to_throw_out_prefix != dog_prefix)
        {
          error_cause.first = "wrong vote";
          error_cause.second = UNEXPECTED_THROW_OUT_PREFIX_IN_CAT_VOTE;
        }
        break;

      case dog_prefix:
        vote_kind = VoteId::KEEP_DOG;
        canonical_dog_id = translatePetId(pet_to_keep,
                                           next_available_dog_id,
                                           dog_translation_tbl);
        canonical_cat_id = translatePetId(pet_to_throw_out,
                                           next_available_cat_id,
                                           cat_translation_tbl);
        if(pet_to_throw_out_prefix != cat_prefix)
        {
          error_cause.first = "wrong vote";
          error_cause.second = UNEXPECTED_THROW_OUT_PREFIX_IN_DOG_VOTE;
        }
        break;

      default:
        error_cause.first = "unkown kind of vote";
        error_cause.second = UNKNOWN_VOTE_KIND;
        break;
    }

    if(error_cause.second != NO_ERROR && (canonical_dog_id > dog_number-1 ||
                                          canonical_cat_id > cat_number-1))
    {
      error_cause.first  = "found more pets than specified";
      error_cause.second = MORE_PETS_THAN_SPECIFIED;
    }
    return error_cause;
  }
};

// Parses the problem specification line
class ProblemSpecificationParser: public LineParser::Parser
{private:
  pet_identifier_t &cat_number, &dog_number, &vote_number;
 public:
  ProblemSpecificationParser(pet_identifier_t &cat_number,
                             pet_identifier_t &dog_number,
                             pet_identifier_t &vote_number):
      cat_number(cat_number),
      dog_number(dog_number),
      vote_number(vote_number)
  {}
  void parse(istream &in)
  {
    in >> trim
       >> cat_number >> trim
       >> dog_number >> trim
       >> vote_number;
  }
  pair<string,ParseErrorCode> getSyntaxError()
  {
    pair<string,ParseErrorCode> error_cause("problem specificiation syntax error",
                                            PROBLEM_SPEC_SYNTAX_ERROR);
    return error_cause;
  }
  pair<string,ParseErrorCode> checkSemantics()
  {
    // We could be strict about the maximum number of votes
    // but the algorithm is not affected by it.
    pair<string,ParseErrorCode> error_cause("", NO_ERROR);
    if(cat_number  > Votes::max_cats_cardinality ||
       dog_number  > Votes::max_dogs_cardinality)
    {
      error_cause.first = "specification surpases expected boundaries";
      error_cause.second = SPEC_SURPASES_BOUNDARIES;
    }
    return error_cause;
  }
};

static Votes& parseProblemInstance(LineParser &line_parser)
{
  // problem specification
  pet_identifier_t cat_number, dog_number, vote_number;
  unsigned int specification_line_number = line_parser.getCurrentLineNumber();

  ProblemSpecificationParser problemSpecificationParser(cat_number, dog_number, vote_number);

  // votes
  VoteId::Kind vote_kind;
  pet_identifier_t pet_to_keep, pet_to_throw_out;

  // vote translation
  // votes are translated to a canonical representation
  // before insertion in order to allow for simple and compact matrix
  // representation: we get the smallest possible ids through translation
  // tables.
  pet_identifier_t canonical_cat_id, canonical_dog_id;
  PetIdTranslationTbl cat_translation_tbl, dog_translation_tbl;
  pet_identifier_t next_available_cat_id = 0;
  pet_identifier_t next_available_dog_id = 0;

  VoteParser voteParser (pet_to_keep, pet_to_throw_out,
                         vote_kind,
                         canonical_cat_id, canonical_dog_id,
                         next_available_cat_id, next_available_dog_id,
                         cat_translation_tbl, dog_translation_tbl,
                         cat_number, dog_number);

  // Get specification and initialize vote containers
  line_parser.parseLine(problemSpecificationParser);
  Votes & votes = *(new Votes(vote_number, cat_number, dog_number));

  while(vote_number-- > 0)
  {
    // parse vote
    line_parser.parseLine(voteParser);

    // insert vote
    if(vote_kind == VoteId::KEEP_CAT)
    {
      votes.for_cats.insertVote(canonical_cat_id,
                                canonical_dog_id,
                                VoteId(vote_kind, pet_to_keep, pet_to_throw_out));
    }
    else
    {
      votes.for_dogs.insertVote(canonical_dog_id,
                                canonical_cat_id,
                                VoteId(vote_kind, pet_to_keep, pet_to_throw_out));
    }
  }

  if(cat_translation_tbl.size() > cat_number ||
     dog_translation_tbl.size() > dog_number)
  {
    throw(ParsingException(specification_line_number,
                           "inconsistent number of pets according to provided votes",
                           MORE_PETS_THAN_SPECIFIED_POST_PARSE));

  }

  return votes;
}

//////////
// MAIN //
//////////

// main function, potentially throwing parsing exceptions
void mainUnsafe()
{
  istream &in  = cin;
  ostream &out = cout;
  vote_count_t maximum_flow;
  vote_count_t maximum_satisfaible_votes;
  static unsigned int total_problem_instances;
  LineParser line_parser(in, 1);
  class _ProblemNumParser: public LineParser::Parser
  {
    void parse(istream &in){ in >> trim >> total_problem_instances;}
    pair<string,ParseErrorCode> getSyntaxError()
    {
      pair<string,ParseErrorCode> error_cause("wrong number of problem instances",
                                              PROBLEM_INSTANCE_NUM_SYNTAX_ERROR);
      return error_cause;
    }
    pair<string,ParseErrorCode> checkSemantics()
    {
      pair<string,ParseErrorCode> error_cause("", NO_ERROR);
      return error_cause;
    }
  } problemNumParser;

  line_parser.parseLine(problemNumParser);

  while(total_problem_instances-- != 0)
  {
    Votes &problem_instance_votes = parseProblemInstance(line_parser);
    FlowNetwork flow_network(problem_instance_votes);
    maximum_flow = flow_network.getMaximumFlow();
    maximum_satisfaible_votes = problem_instance_votes.total_votes - maximum_flow;
    out << maximum_satisfaible_votes  << endl;
    delete &problem_instance_votes;
  }
}

// wrapper capturing and printing parsing errors
int main()
{
  int ret = 0;
  try
  {
    mainUnsafe();
  }
  catch(ParsingException e)
  {
    cerr << "Parsing error at line " << e.lineNumber() << ": "
         << e.getErrorDescription() << "." << endl;
    ret = e.getParseErrorCode();
  }
  return ret;
}
