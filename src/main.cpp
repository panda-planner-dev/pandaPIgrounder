#include <fstream>
#include <iostream>

#include <cerrno>
#include <cstring>

#include <unistd.h>
#include <getopt.h>

#include "debug.h"
#include "model.h"
#include "parser.h"
#include "planning-graph.h"
#include "naiveGrounding.h"

int main (int argc, char * argv[])
{
	struct option options[] = {
		{"debug",           no_argument,    NULL,   'd'},
		{"print-domain",    no_argument,    NULL,   'p'},
		{"naive-grounding", no_argument,    NULL,   'n'},
		{"quiet",           no_argument,    NULL,   'q'},
		{"planning-graph",  no_argument,    NULL,   'r'},
		{NULL,              0,              NULL,   0},
	};

	bool quietMode = false;
	bool debugMode = false;
	bool printDomainMode = false;
	bool doNaiveGrounding = false;
	bool doPlanningGraph = false;

	bool optionsValid = true;
	while (true)
	{
		int c = getopt_long (argc, argv, "dpnqr", options, NULL);
		if (c == -1)
			break;
		if (c == '?' || c == ':')
		{
			// Invalid option; getopt_long () will print an error message
			optionsValid = false;
			continue;
		}

		if (c == 'd')
			debugMode = true;
		else if (c == 'p')
			printDomainMode = true;
		else if (c == 'n')
			doNaiveGrounding = true;
		else if (c == 'q')
			quietMode = true;
		else if (c == 'r')
			doPlanningGraph = true;
	}
	int nArgs = argc - optind;

	if (!optionsValid)
	{
		std::cout << "Invalid options. Exiting." << std::endl;
		return 1;
	}

	if (debugMode)
		setDebugMode (debugMode);

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

		Domain data;
		Problem problem;
		bool success = readInput (*inputStream, data, problem);

		if (!success)
		{
			std::cerr << "Failed to read input data!" << std::endl;
			return 1;
		}
		if (!quietMode)
			std::cerr << "Parsing done." << std::endl;

		if (printDomainMode)
			printDomainAndProbem (data, problem);
		if (doNaiveGrounding)
			naiveGrounding(data, problem);
		if (doPlanningGraph)
			doAndPrintPlanningGraph (data, problem);
	}
}
