#include <algorithm>
#include <iostream>
#include <set>
#include <vector>

#include <cassert>

#include "debug.h"
#include "model.h"
#include "hierarchy-typing.h"

template<typename T>
static std::set<T> intersect (const std::set<T> & a, const std::set<T> & b)
{
	std::set<T> result;
	std::set_intersection (a.begin (), a.end (), b.begin (), b.end (), std::inserter (result, result.begin ()));
	return result;
}

/**
 * @brief Reduces the set of possible constants for a task/method by applying variable constraints.
 *
 * If a constraint requires that variables a and b be equal, then only those constants that are valid for both a and b are valid.
 * If a constraint requires that variables a and b *not* be equal, and there is only one allowed value for a, then we can remove the allowed value for a from the set of allowed values for b (or vice versa).
 *
 * This function will repeatedly apply the constraints until these rules yield no further reduction.
 */
static void applyConstraints (PossibleConstants & possibleConstants, const std::vector<VariableConstraint> & constraints)
{
	bool changed;
	do
	{
		changed = false;
		for (const VariableConstraint & constraint : constraints)
		{
			if (constraint.type == VariableConstraint::Type::EQUAL)
			{
				// Both variables must be equal; reduce the set of possible constants to the intersection.
				const auto & intersection = intersect (possibleConstants[constraint.var1], possibleConstants[constraint.var2]);

				// Comparing the size of the sets is faster than comparing the sets themselves
				if (intersection.size () < possibleConstants[constraint.var1].size () || intersection.size () < possibleConstants[constraint.var2].size ())
					changed = true;

				possibleConstants[constraint.var1] = intersection;
				possibleConstants[constraint.var2] = intersection;
			}
			else if (constraint.type == VariableConstraint::Type::NOT_EQUAL)
			{
				// Both variables may not be equal; if any of them only has one possible value, remove it from the other.
				size_t erased = 0;
				if (possibleConstants[constraint.var1].size () == 1)
					erased += possibleConstants[constraint.var2].erase (*possibleConstants[constraint.var1].begin ());
				if (possibleConstants[constraint.var2].size () == 1)
					erased += possibleConstants[constraint.var1].erase (*possibleConstants[constraint.var2].begin ());

				if (erased > 0)
					changed = true;
			}
		}
	}
	while (changed);
}

HierarchyTyping::HierarchyTyping (const Domain & domain, const Problem & problem) : possibleConstantsPerTask (domain.nTotalTasks), possibleConstantsPerMethod (domain.decompositionMethods.size ())
{
	const Task & topTask = domain.tasks[problem.initialAbstractTask];

	// Initially determine possible constants for the top task
	PossibleConstants topTaskPossibleConstants (topTask.variableSorts.size ());
	for (size_t varIdx = 0; varIdx < topTask.variableSorts.size (); ++varIdx)
		topTaskPossibleConstants[varIdx] = domain.sorts[varIdx].members;
	applyConstraints (topTaskPossibleConstants, topTask.variableConstraints);

	// Start the DFS at the top task
	taskDfs (domain, problem.initialAbstractTask, topTaskPossibleConstants);
}

void HierarchyTyping::taskDfs (const Domain & domain, size_t taskNo, PossibleConstants possibleConstants)
{
	const Task & task = domain.tasks[taskNo];

	// Stop recursion if we already found this set of possible constants
	for (const auto & visitedConstants : possibleConstantsPerTask[taskNo])
	{
		assert (visitedConstants.size () == task.variableSorts.size ());

		bool visited = true;
		for (size_t varIdx = 0; varIdx < task.variableSorts.size (); ++varIdx)
		{
			if (!std::includes (visitedConstants[varIdx].begin (), visitedConstants[varIdx].end (), possibleConstants[varIdx].begin (), possibleConstants[varIdx].end ()))
			{
				visited = false;
				break;
			}
		}

		if (visited)
			return;
	}
	possibleConstantsPerTask[taskNo].push_back (possibleConstants);

	for (int methodNo : task.decompositionMethods)
	{
		const DecompositionMethod & method = domain.decompositionMethods[methodNo];
		assert (task.variableSorts.size () == method.taskParameters.size ());

		// Determine possible constants for this method
		PossibleConstants possibleMethodConstants (method.variableSorts.size ());
		for (size_t methodVarIdx = 0; methodVarIdx < method.variableSorts.size (); ++methodVarIdx)
		{
			// Initially, we can use all constants from the method variable's sort.
			int sort = method.variableSorts[methodVarIdx];
			possibleMethodConstants[methodVarIdx] = domain.sorts[sort].members;
		}
		for (size_t taskVarIdx = 0; taskVarIdx < method.taskParameters.size (); ++taskVarIdx)
		{
			// For method variables that correspond to task variables, we intersect the possible constants.
			int methodVarIdx = method.taskParameters[taskVarIdx];
			possibleMethodConstants[methodVarIdx] = intersect (possibleMethodConstants[methodVarIdx], possibleConstants[taskVarIdx]);
		}
		applyConstraints (possibleMethodConstants, method.variableConstraints);

		// If we have no valid assignment for a variable, we cannot instantiate this method.
		if (std::any_of (possibleMethodConstants.begin (), possibleMethodConstants.end (), [](const auto & possibleValues) { return possibleValues.size () == 0; }))
			continue;

		possibleConstantsPerMethod[methodNo].push_back (possibleMethodConstants);

		for (const auto & subtask : method.subtasks)
		{
			assert (subtask.arguments.size () == domain.tasks[subtask.taskNo].variableSorts.size ());

			PossibleConstants possibleSubtaskConstants (subtask.arguments.size ());
			for (size_t subtaskVarIdx = 0; subtaskVarIdx < subtask.arguments.size (); ++subtaskVarIdx)
			{
				int methodVarIdx = subtask.arguments[subtaskVarIdx];
				possibleSubtaskConstants[subtaskVarIdx] = possibleMethodConstants[methodVarIdx];
			}
			applyConstraints (possibleSubtaskConstants, domain.tasks[subtask.taskNo].variableConstraints);

			taskDfs (domain, subtask.taskNo, possibleSubtaskConstants);
		}
	}
}

static bool isAssignmentCompatible (const std::vector<PossibleConstants> & possibleConstants, const VariableAssignment & assignedVariables)
{
	for (const auto & possibleConstants : possibleConstants)
	{
		bool valid = true;
		for (size_t varIdx = 0; varIdx < possibleConstants.size (); ++varIdx)
		{
			int varValue = assignedVariables[varIdx];
			if (possibleConstants[varIdx].count (varValue) == 0)
			{
				valid = false;
				break;
			}
		}
		if (valid)
			return true;

	}
	return false;
}

template<>
bool HierarchyTyping::isAssignmentCompatible<Task> (int taskNo, const VariableAssignment & assignedVariables) const
{
	return ::isAssignmentCompatible (possibleConstantsPerTask[taskNo], assignedVariables);
}

template<>
bool HierarchyTyping::isAssignmentCompatible<DecompositionMethod> (int methodNo, const VariableAssignment & assignedVariables) const
{
	return ::isAssignmentCompatible (possibleConstantsPerMethod[methodNo], assignedVariables);
}
