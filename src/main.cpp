#include <fstream>
#include <iostream>
#include <map>
#include <memory>

#include <cerrno>
#include <cstring>

#include <unistd.h>
#include <getopt.h>

#include "main.h"
#include "debug.h"
#include "grounding.h"
#include "hierarchy-typing.h"
#include "model.h"
#include "parser.h"

int main (int argc, char * argv[])
{
	struct option options[] = {
		{"output-domain",      	                            no_argument,    NULL,   'O'},
		{"primitive",          	                            no_argument,    NULL,   'P'},
		{"debug",              	                            no_argument,    NULL,   'd'},
		{"print-domain",       	                            no_argument,    NULL,   'p'},
		{"quiet",              	                            no_argument,    NULL,   'q'},
		{"print-timings",     	                            no_argument,    NULL,   't'},
		{"invariants",         	                            no_argument,    NULL,   'i'},
		{"force-sas-only",    	                            no_argument,    NULL,   'S'},
		{"no-sas-deletes",    	                            no_argument,    NULL,   'n'},
		{"all-sas-deletes",    	                            no_argument,    NULL,   'a'},
		{"force-sas-only",    	                            no_argument,    NULL,   'S'},
		{"compile-negative-sas",                            no_argument,    NULL,   'N'},
		{"only-ground",         	                        no_argument,    NULL,   'g'},
		{"output-hddl",         	                        no_argument,    NULL,   'H'},
		{"h2", 			        	                        no_argument,    NULL,   '2'},
		{"sasplus", 	        	                        no_argument,    NULL,   's'},
		{"remove-duplicates",      	                        no_argument,    NULL,   'D'},
		{"noop-for-empty-methods",                          no_argument,    NULL,   'E'},
		{"two-tasks-per-method",                            no_argument,    NULL,   't'},
		
		{"no-hierarchy-typing",	                            no_argument,    NULL,   'h'},
		{"no-literal-pruning", 	                            no_argument,    NULL,   'l'},
		{"no-abstract-expansion",                           no_argument,    NULL,   'e'},
		{"no-method-precondition-pruning",                  no_argument,    NULL,   'm'},
		{"future-caching-by-initially-matched-precondition",no_argument,    NULL,   'f'},
		{"static-preconditions-in-hierarchy-typing"		   ,no_argument,    NULL,   'c'},

		
		{NULL,                            0,              NULL,   0},
	};

	bool primitiveMode = false;
	grounding_configuration config;
	
	
	bool debugMode = false;
	bool optionsValid = true;
	
	bool outputDomain = false;

	while (true)
	{
		int c = getopt_long_only (argc, argv, "dpqiOPhlemgft2sHSNnaDEct", options, NULL);
		if (c == -1)
			break;
		if (c == '?' || c == ':')
		{
			// Invalid option; getopt_long () will print an error message
			optionsValid = false;
			continue;
		}

		if (c == 'P')
			primitiveMode = true;
		else if (c == 'd')
			debugMode = true;
		else if (c == 'p')
			outputDomain = true;
		else if (c == 'q')
			config.quietMode = true;
		else if (c == 'i')
			config.computeInvariants = true;
		else if (c == 'S')
			config.outputSASVariablesOnly = true;
		else if (c == 'n')
			config.sas_mode = SAS_NONE;
		else if (c == 'a')
			config.sas_mode = SAS_ALL;
		else if (c == 'N')
			config.compileNegativeSASVariables = true;
		else if (c == 'D')
			config.removeDuplicateActions = true;
		else if (c == 'E')
			config.noopForEmptyMethods = true;
		else if (c == 't')
			config.atMostTwoTasksPerMethod = true;
		else if (c == 'O')
			outputDomain = true;
		
		else if (c == 'H')
			config.outputHDDL = true;
		
		else if (c == 'h')
			config.enableHierarchyTyping = false;
		else if (c == 'l')
			config.removeUselessPredicates = false;
		else if (c == 'e')
			config.expandChoicelessAbstractTasks = false;
		else if (c == 'm')
			config.pruneEmptyMethodPreconditions = false;
		else if (c == 'g')
			config.outputForPlanner = false;
		else if (c == 'f')
			config.futureCachingByPrecondition = true;
		else if (c == 'c')
			config.withStaticPreconditionChecking = true;
		else if (c == 't')
			config.printTimings = true;
		else if (c == '2')
			config.h2Mutexes = true;
		else if (c == 's')
			config.outputSASPlus = true;
	}
	
	if (!optionsValid)
	{
		std::cout << "Invalid options. Exiting." << std::endl;
		return 1;
	}

	if (!config.removeUselessPredicates && config.h2Mutexes){
		std::cout << "To use H2-mutexes, useless predicates must be removed, else the H2 preprocessor may crash ..." << std::endl;
		return 1;
	}

	if (debugMode)
		setDebugMode (debugMode);

	if (primitiveMode && !config.quietMode)
		std::cerr << "Note: Running in benchmark mode; grounding results will not be printed." << std::endl;

	std::vector<std::string> inputFiles;
	for (int i = optind; i < argc; ++i)
	{
		inputFiles.push_back (argv[i]);
	}

	std::string inputFilename = "-";
	std::string outputFilename = "-";
	std::string outputFilename2 = "-";

	if (inputFiles.size() > 3){
		std::cerr << "You may specify at most two files as parameters: the input and two output file" << std::endl;
		return 1;
	} else {
		if (inputFiles.size())
			inputFilename = inputFiles[0];
		if (inputFiles.size() > 1)
			outputFilename = inputFiles[1];
		if (inputFiles.size() > 2)
			outputFilename2 = inputFiles[2];
	}

	std::istream * inputStream;
	if (inputFilename == "-")
	{
		if (!config.quietMode)
			std::cerr << "Reading input from standard input." << std::endl;

		inputStream = &std::cin;
	}
	else
	{
		if (!config.quietMode)
			std::cerr << "Reading input from " << inputFilename << "." << std::endl;

		std::ifstream * fileInput  = new std::ifstream(inputFilename);
		if (!fileInput->good())
		{
			std::cerr << "Unable to open input file " << inputFilename << ": " << strerror (errno) << std::endl;
			return 1;
		}

		inputStream = fileInput;
	}


	Domain domain;
	Problem problem;
	bool success = readInput (*inputStream, domain, problem);

	std::ostream * outputStream;
	if (outputFilename == "-")
	{
		if (!config.quietMode)
			std::cerr << "Writing output to standard output." << std::endl;

		outputStream = &std::cout;
	}
	else
	{
		if (!config.quietMode)
			std::cerr << "Writing output to " << outputFilename << "." << std::endl;

		std::ofstream * fileOutput  = new std::ofstream(outputFilename);

		if (!fileOutput->good ())
		{
			std::cerr << "Unable to open output file " << outputFilename << ": " << strerror (errno) << std::endl;
			return 1;
		}

		outputStream = fileOutput;
	}

	std::ostream * outputStream2;
	if (outputFilename2 == "-")
	{
		if (!config.quietMode)
			std::cerr << "Writing output to standard output." << std::endl;

		outputStream2 = &std::cout;
	}
	else
	{
		if (!config.quietMode)
			std::cerr << "Writing output to " << outputFilename2 << "." << std::endl;

		std::ofstream * fileOutput  = new std::ofstream(outputFilename2);

		if (!fileOutput->good ())
		{
			std::cerr << "Unable to open output file " << outputFilename << ": " << strerror (errno) << std::endl;
			return 1;
		}

		outputStream2 = fileOutput;
	}

	if (!success)
	{
		std::cerr << "Failed to read input data!" << std::endl;
		return 1;
	}
	if (!config.quietMode)
		std::cerr << "Parsing done." << std::endl;

	if (outputDomain)
	{
		printDomainAndProblem (domain, problem);
		return 1;
	}

	// Run the actual grounding procedure
	if (primitiveMode)
	{
		// Just run the PG - this is for speed testing
		std::unique_ptr<HierarchyTyping> hierarchyTyping;
		if (config.enableHierarchyTyping)
			hierarchyTyping = std::make_unique<HierarchyTyping> (domain, problem, config, false, true);

		std::cout << hierarchyTyping.get()->graphToDotString(domain);
	}
	else
	{
		run_grounding (domain, problem, *outputStream, *outputStream2, config);
	}

}
