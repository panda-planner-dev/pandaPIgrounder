#ifndef PLANNING_GRAPH_H_INCLUDED
#define PLANNING_GRAPH_H_INCLUDED

/**
 * @defgroup planning-graph Planning Graph
 *
 * @{
 */

#include <set>
#include <vector>

#include "model.h"

/**
 * Runs the planning graph and returns the grounded tasks and facts in the given output arguments.
 */
void runPlanningGraph (std::vector<GroundedTask> & outputTasks, std::set<Fact> & outputFacts, const Domain & domain, const Problem & problem, bool enableHierarchyTyping);

/**
 * Runs the planning graph and prints the output in the correct output format.
 */
void doAndPrintPlanningGraph (const Domain & domain, const Problem & problem, bool enableHierarchyTyping);

/**
 * @}
 */

#endif
