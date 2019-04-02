#include <fstream>
#include <iostream>
#include <map>

#include <cerrno>
#include <cstring>

#include <unistd.h>
#include <getopt.h>

#include "debug.h"
#include "hierarchy-typing.h"
#include "model.h"
#include "naiveGrounding.h"
#include "parser.h"
#include "planning-graph.h"

enum RunMode
{
	RUN_MODE_PLANNING_GRAPH,
	RUN_MODE_NAIVE_GROUNDING,
	RUN_MODE_PRINT_DOMAIN,

	RUN_MODE_DEFAULT = RUN_MODE_PLANNING_GRAPH,
};

const std::map<RunMode, std::string> runModes =
	{
		{RUN_MODE_PRINT_DOMAIN,     "Print Domain"},
		{RUN_MODE_NAIVE_GROUNDING,  "Naive Grounding"},
		{RUN_MODE_PLANNING_GRAPH,   "Planning Graph"},
	}
;

int main (int argc, char * argv[])
{
	struct option options[] = {
		{"benchmark",           no_argument,    NULL,   'b'},
		{"debug",               no_argument,    NULL,   'd'},
		{"hierarchy-typing",    no_argument,    NULL,   'h'},
		{"naive-grounding",     no_argument,    NULL,   'n'},
		{"print-domain",        no_argument,    NULL,   'p'},
		{"quiet",               no_argument,    NULL,   'q'},
		{"planning-graph",      no_argument,    NULL,   'r'},
		{NULL,                  0,              NULL,   0},
	};

	bool benchmarkMode = false;
	bool quietMode = false;
	bool debugMode = false;
	bool enableHierarchyTyping = false;

	bool optionsValid = true;
	std::set<RunMode> selectedModes;
	while (true)
	{
		int c = getopt_long (argc, argv, "bdhnpqr", options, NULL);
		if (c == -1)
			break;
		if (c == '?' || c == ':')
		{
			// Invalid option; getopt_long () will print an error message
			optionsValid = false;
			continue;
		}

		if (c == 'b')
			benchmarkMode = true;
		else if (c == 'd')
			debugMode = true;
		else if (c == 'h')
			enableHierarchyTyping = true;
		else if (c == 'n')
			selectedModes.insert (RUN_MODE_NAIVE_GROUNDING);
		else if (c == 'p')
			selectedModes.insert (RUN_MODE_PRINT_DOMAIN);
		else if (c == 'q')
			quietMode = true;
		else if (c == 'r')
			selectedModes.insert (RUN_MODE_PLANNING_GRAPH);
	}
	int nArgs = argc - optind;

	if (!optionsValid)
	{
		std::cout << "Invalid options. Exiting." << std::endl;
		return 1;
	}

	// Check if mutually exclusive modes were selected
	RunMode runMode = RUN_MODE_DEFAULT;
	if (selectedModes.size () > 1)
	{
		std::cout << "Cannot enable mutually exclusive run modes: ";
		size_t printed = 0;
		for (const auto runMode : selectedModes)
		{
			if (printed > 0)
				std::cout << ", ";
			std::cout << runModes.at (runMode);
			++printed;
		}
		std::cout << std::endl;
		return 1;
	}
	else if (selectedModes.size () == 0)
	{
		if (!quietMode)
			std::cerr << "No run mode selected; selecting \"" << runModes.at (RUN_MODE_DEFAULT) << "\" mode." << std::endl;
	}
	else
	{
		runMode = *selectedModes.begin ();
	}

	if (debugMode)
		setDebugMode (debugMode);

	if (benchmarkMode && !quietMode)
		std::cerr << "Note: Running in benchmark mode; grounding results will not be printed." << std::endl;

	std::vector<std::string> inputFiles;
	if (nArgs < 1)
	{
		inputFiles.push_back ("-");
	}
	else
	{
		for (int i = optind; i < argc; ++i)
		{
			inputFiles.push_back (argv[i]);
		}
	}

	for (std::string inputFilename : inputFiles)
	{
		std::istream * inputStream;
		std::ifstream fileInput;
		if (inputFilename == "-")
		{
			if (!quietMode)
				std::cerr << "Reading input from standard input." << std::endl;

			inputStream = &std::cin;
		}
		else
		{
			if (!quietMode)
				std::cerr << "Reading input from " << inputFilename << "." << std::endl;

			fileInput.open (inputFilename);

			if (!fileInput.good ())
			{
				std::cerr << "Unable to open input file " << inputFilename << ": " << strerror (errno) << std::endl;
				return 1;
			}

			inputStream = &fileInput;
		}

		Domain domain;
		Problem problem;
		bool success = readInput (*inputStream, domain, problem);

		if (!success)
		{
			std::cerr << "Failed to read input data!" << std::endl;
			return 1;
		}
		if (!quietMode)
			std::cerr << "Parsing done." << std::endl;

		if (runMode == RUN_MODE_PRINT_DOMAIN)
		{
			printDomainAndProblem (domain, problem);
		}
		else if (runMode == RUN_MODE_NAIVE_GROUNDING)
		{
			naiveGrounding (domain, problem);
		}
		else if (runMode == RUN_MODE_PLANNING_GRAPH)
		{
			if (benchmarkMode)
			{
				// Run PG without printing output
				std::vector<GroundedTask> groundedTasks;
				std::set<Fact> reachableFacts;
				runPlanningGraph (groundedTasks, reachableFacts, domain, problem, enableHierarchyTyping);
			}
			else
			{
				doAndPrintPlanningGraph (domain, problem, enableHierarchyTyping);
			}
		}
	}
}
