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
#include "givenPlan.h"


#include "cmdline.h"

int main (int argc, char * argv[])
{
	gengetopt_args_info args_info;
	if (cmdline_parser(argc, argv, &args_info) != 0) return 1;

	// set debug mode
	if (args_info.debug_given) setDebugMode(true);

	
	grounding_configuration config;
	// this flag is not accessible from the command line; only for debugging
	bool primitiveMode = false;
	bool outputDomain = false;

	outputDomain = args_info.output_domain_flag;

	config.quietMode = args_info.quiet_flag;
	config.printTimings = args_info.print_timings_flag;

	config.computeInvariants = args_info.invariants_flag;
	config.h2Mutexes = args_info.h2_flag;

	// SAS mode
	config.sas_mode = SAS_AS_INPUT;
	if (args_info.no_sas_deletes_given) config.sas_mode = SAS_NONE;
	if (args_info.all_sas_deletes_given) config.sas_mode = SAS_ALL;

	// type of output (default is for planner)
	if (args_info.sasplus_given) config.outputSASPlus = true, config.outputForPlanner = false;
	if (args_info.hddl_given) config.outputHDDL = true, config.outputForPlanner = false;
	if (args_info.no_output_given) config.outputForPlanner = false;
	
	config.outputSASVariablesOnly = args_info.force_sas_flag;
	config.compileNegativeSASVariables = args_info.compile_negative_flag;

	// transformations
	config.removeDuplicateActions = args_info.dont_remove_duplicates_flag;
	config.noopForEmptyMethods = args_info.no_empty_compilation_flag;
	config.removeUselessPredicates = args_info.no_literal_pruning_flag;
	config.expandChoicelessAbstractTasks = args_info.no_abstract_expansion_flag;
	config.keepTwoRegularisation = args_info.keep_two_regularisation_flag;
	config.pruneEmptyMethodPreconditions = args_info.no_method_precondition_pruning_flag;
	config.compactConsecutivePrimitives = args_info.compactify_actions_flag;

	config.atMostTwoTasksPerMethod = args_info.two_regularisation_flag;
	
	// algorithmic options for grounding
	config.enableHierarchyTyping = args_info.no_hierarchy_typing_flag;
	config.futureCachingByPrecondition = args_info.future_caching_by_initially_matched_precondition_flag;
	config.withStaticPreconditionChecking = args_info.static_precondition_checking_in_hierarchy_typing_flag;	

	config.print_options();	

	if (!config.removeUselessPredicates && config.h2Mutexes){
		std::cout << "To use H2-mutexes, useless predicates must be removed, else the H2 preprocessor may crash ..." << std::endl;
		return 1;
	}

	if (primitiveMode && !config.quietMode)
		std::cerr << "Note: Running in benchmark mode; grounding results will not be printed." << std::endl;

	std::vector<std::string> inputFiles;
	for (unsigned i = 0 ; i < args_info.inputs_num; i++)
    	inputFiles.push_back(args_info.inputs[i]);

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


	given_plan_typing_information given_typing_info;
	if (args_info.plan_given){
		std::string plan_filename(args_info.plan_orig);
		given_typing_info = extract_given_plan_typer(domain,problem,plan_filename);
	}



	// Run the actual grounding procedure
	if (primitiveMode)
	{
		// Just run the PG - this is for speed testing
		std::unique_ptr<HierarchyTyping> hierarchyTyping;
		if (config.enableHierarchyTyping)
			hierarchyTyping = std::make_unique<HierarchyTyping> (domain, problem, config, given_typing_info, false, true);

		std::cout << hierarchyTyping.get()->graphToDotString(domain);
	}
	else
	{
		run_grounding (domain, problem, *outputStream, *outputStream2, config, given_typing_info);
	}

}
