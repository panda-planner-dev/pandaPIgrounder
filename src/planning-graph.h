#ifndef PLANNING_GRAPH_H_INCLUDED
#define PLANNING_GRAPH_H_INCLUDED

/**
 * @defgroup planning-graph Planning Graph
 *
 * @{
 */

#include <set>
#include <vector>

/**
 * @brief A grounded task instance.
 */
struct GroundedTask
{
	/// The number of the task.
	int taskNo;

	/// The arguments for the grounded task.
	std::vector<int> arguments;
};

/**
 * Runs the planning graph and returns the grounded tasks and facts in the given output arguments.
 */
void runPlanningGraph (std::vector<GroundedTask> & outputTasks, std::set<Fact> & outputFacts, const Domain & domain, const Problem & problem);

/**
 * Runs the planning graph and prints the output in the correct output format.
 */
void doAndPrintPlanningGraph (const Domain & domain, const Problem & problem);

/**
 * @}
 */

#endif
