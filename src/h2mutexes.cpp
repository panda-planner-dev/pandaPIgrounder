#define NO_OPERATOR

#include "h2mutexes.h"
#include "../h2-fd-preprocessor/src/domain_transition_graph.h"
#include "../h2-fd-preprocessor/src/state.h"
#include "../h2-fd-preprocessor/src/mutex_group.h"
#include "../h2-fd-preprocessor/src/operator.h"
#include "../h2-fd-preprocessor/src/axiom.h"


void h2_mutexes(const Domain & domain, const Problem & problem,
		std::vector<Fact> & reachableFacts,
		std::vector<GroundedTask> & reachableTasks,
		std::vector<bool> & prunedFacts,
		std::vector<bool> & prunedTasks,
		bool quietMode){

	bool metric;
	std::vector<Variable *> variables;
	std::vector<Variable> internal_variables;
    State initial_state;
	std::vector<std::pair<Variable *, int>> goals;
	std::vector<MutexGroup> mutexes;
	std::vector<Operator> operators;
	std::vector<Axiom> axioms;
	std::vector<DomainTransitionGraph> transition_graphs;

}


