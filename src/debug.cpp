#include <iostream>
#include <string>

#include "debug.h"

static bool debugMode = false;

std::string color (Color color, std::string text)
{
	return std::string ()
		+ "\033[" + std::to_string (30 + color) + "m"
		+ text
		+ "\033[m"
	;
}

void printFact (const Domain & domain, const Fact & fact)
{
	const Predicate & predicate = domain.predicates[fact.predicateNo];
	std::cerr << "    " << color (CYAN, predicate.name);

	for (size_t argumentIdx = 0; argumentIdx < fact.arguments.size (); ++argumentIdx)
	{
		std::cerr << " <" << color (YELLOW, domain.constants[fact.arguments[argumentIdx]]) << ">";
	}
	std::cerr << std::endl;
}

void printTask (const Domain & domain, const Task & task, bool printDecompositionMethods)
{
	// Print task name and variable sorts
	std::cerr << "    " << color (BLUE, task.name);
	int nVariables = task.variableSorts.size ();
	for (int variableIdx = 0; variableIdx < nVariables; ++variableIdx)
	{
		std::cerr << " <" << color (YELLOW, domain.sorts[task.variableSorts[variableIdx]].name) << ">";
	}
	std::cerr << std::endl;

	if (printDecompositionMethods)
	{
		// Print all decomposition methods
		int nMethods = task.decompositionMethods.size ();
		for (int methodIdx = 0; methodIdx < nMethods; ++methodIdx)
		{
			// Print method name and variable sorts
			const DecompositionMethod & method = task.decompositionMethods[methodIdx];
			std::cerr << "        " << color (GREEN, method.name);
			int nVariables = method.variableSorts.size ();
			for (int variableIdx = 0; variableIdx < nVariables; ++variableIdx)
			{
				std::cerr << " <" << color (YELLOW, domain.sorts[method.variableSorts[variableIdx]].name);
				std::cerr << "-" << color (CYAN, std::string () + ((char) ('A' + variableIdx))) << ">";
			}
			std::cerr << std::endl;

			// Print all subtasks
			int nSubtasks = method.subtasks.size ();
			for (int subtaskIdx = 0; subtaskIdx < nSubtasks; ++subtaskIdx)
			{
				const TaskWithArguments & taskWithArguments = method.subtasks[subtaskIdx];
				std::cerr << "            " << color (CYAN, domain.tasks[taskWithArguments.taskNo].name);

				const Task & subtask = domain.tasks[taskWithArguments.taskNo];
				int nSubtaskVariables = subtask.variableSorts.size ();
				for (int variableIdx = 0; variableIdx < nSubtaskVariables; ++variableIdx)
				{
					std::cerr << " <" << color (YELLOW, domain.sorts[subtask.variableSorts[variableIdx]].name);
					std::cerr << "-" << color (CYAN, std::string () + ((char) ('A' + taskWithArguments.arguments[variableIdx]))) << ">";
				}
				std::cerr << std::endl;
			}
		}
	}
}

void printDomainAndProbem (const Domain & domain, const Problem & problem)
{
	DEBUG (std::cerr << "Domain has [" << domain.constants.size () << "] constants and [" << domain.sorts.size () << "] sorts." << std::endl);
	DEBUG (std::cerr << "Domain has [" << domain.nPrimitiveTasks << "] primitive and [" << domain.nAbstractTasks << "] abstract tasks." << std::endl);

	std::cerr << "Tasks with methods:" << std::endl;
	for (int taskIdx = 0; taskIdx < domain.nPrimitiveTasks + domain.nAbstractTasks; ++taskIdx)
		printTask (domain, domain.tasks[taskIdx], true);

	std::cerr << std::endl;
	std::cerr << "Initial state:" << std::endl;
	for (size_t factIdx = 0; factIdx < problem.init.size (); ++factIdx)
		printFact (domain, problem.init[factIdx]);

	std::cerr << std::endl;
	std::cerr << "Goal state:" << std::endl;
	for (size_t factIdx = 0; factIdx < problem.goal.size (); ++factIdx)
		printFact (domain, problem.goal[factIdx]);

	std::cerr << std::endl;
	std::cerr << "Initial abstract task: " << color (BLUE, domain.tasks[problem.initialAbstractTask].name) << std::endl;
}

bool getDebugMode (void)
{
	return debugMode;
}

void setDebugMode (bool enabled)
{
#ifdef DEBUG_MODE
	debugMode = enabled;
#else
	if (enabled)
	{
		std::cerr << "Tried to enable debug mode, but the program was built with debugging disabled." << std::endl;
	}
#endif
}
