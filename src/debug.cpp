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

void printDomain (Domain & domain)
{
	DEBUG (std::cerr << "Domain has [" << domain.constants.size () << "] constants and [" << domain.sorts.size () << "] sorts." << std::endl);
	DEBUG (std::cerr << "Domain has [" << domain.nPrimitiveTasks << "] primitive and [" << domain.nAbstractTasks << "] abstract tasks." << std::endl);

	std::cerr << "Tasks with methods:" << std::endl;
	for (int taskIdx = 0; taskIdx < domain.nPrimitiveTasks + domain.nAbstractTasks; ++taskIdx)
	{
		// Print task name and variable sorts
		Task & task = domain.tasks[taskIdx];
		std::cerr << "    " << color (BLUE, task.name);
		int nVariables = task.variableSorts.size ();
		for (int variableIdx = 0; variableIdx < nVariables; ++variableIdx)
		{
			std::cerr << " <" << color (YELLOW, domain.sorts[task.variableSorts[variableIdx]].name) << ">";
		}
		std::cerr << std::endl;

		// Print all decomposition methods
		int nMethods = task.decompositionMethods.size ();
		for (int methodIdx = 0; methodIdx < nMethods; ++methodIdx)
		{
			// Print method name and variable sorts
			DecompositionMethod & method = task.decompositionMethods[methodIdx];
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
				TaskWithArguments & taskWithArguments = method.subtasks[subtaskIdx];
				std::cerr << "            " << color (CYAN, domain.tasks[taskWithArguments.taskNo].name);

				Task & subtask = domain.tasks[taskWithArguments.taskNo];
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
