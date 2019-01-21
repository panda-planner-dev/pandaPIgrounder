#include <cassert>
#include <fstream>
#include <functional>
#include <iostream>
#include <sstream>

#include "debug.h"
#include "model.h"
#include "parser.h"

template <typename T>
using ReadFunction = void (const Domain & state, std::istream & input, T & output);

/**
 * @brief Read count elements from input into outputVector using readFunc.
 */
template <typename T>
void readN (const Domain & state, std::istream & input, std::vector<T> & outputVector, ReadFunction<T> & readFunc, size_t count)
{
	outputVector.resize (count);
	for (size_t i = 0; i < count; ++i)
		readFunc (state, input, outputVector[i]);
}

/**
 * @brief Read the number of elements, then read the elements from input into outputVector using readFunc.
 */
template <typename T>
void readMultiple (const Domain & state, std::istream & input, std::vector<T> & outputVector, ReadFunction<T> & readFunc)
{
	size_t count;
	input >> count;

	readN (state, input, outputVector, readFunc, count);
}

/**
 * @brief Read a primitive value from input into output.
 */
template <typename T>
void readPrimitive (const Domain & state, std::istream & input, T & output)
{
	input >> output;
}

void failIfNotSatisfied (bool condition, std::string message)
{
	if (!condition)
		throw BadInputException (message);
}

void readSort (const Domain & state, std::istream & input, Sort & outputSort)
{
	input >> outputSort.name;
	readMultiple (state, input, outputSort.members, readPrimitive);
}

void readPredicate (const Domain & state, std::istream & input, Predicate & outputPredicate)
{
	input >> outputPredicate.name;
	readMultiple (state, input, outputPredicate.argumentSorts, readPrimitive);
}

void readPredicateWithArguments (const Domain & state, std::istream & input, PredicateWithArguments & outputPredicate)
{
	input >> outputPredicate.predicateNo;

	size_t nArguments = state.predicates[outputPredicate.predicateNo].argumentSorts.size ();
	readN (state, input, outputPredicate.arguments, readPrimitive, nArguments);
}

void readFact (const Domain & state, std::istream & input, Fact & fact)
{
	input >> fact.predicateNo;

	size_t nArguments = state.predicates[fact.predicateNo].argumentSorts.size ();
	readN (state, input, fact.arguments, readPrimitive, nArguments);
}

void readTaskWithArguments (const Domain & state, std::istream & input, TaskWithArguments & outputTaskWithArguments)
{
	input >> outputTaskWithArguments.taskNo;

	size_t nArguments = state.tasks[outputTaskWithArguments.taskNo].variableSorts.size ();
	readN (state, input, outputTaskWithArguments.arguments, readPrimitive, nArguments);
}

void readVariableConstraint (const Domain & state, std::istream & input, VariableConstraint & outputConstraint)
{
	std::string constraintType;
	input >> constraintType;

	failIfNotSatisfied (constraintType == "=" || constraintType == "!=", "Constraint type must be \"=\" (equal) or \"!=\" (not equal); \"" + constraintType + "\" given");

	if (constraintType == "=")
		outputConstraint.type = VariableConstraint::Type::EQUAL;
	else
		outputConstraint.type = VariableConstraint::Type::NOT_EQUAL;

	input >> outputConstraint.var1 >> outputConstraint.var2;
}

void readPrimitiveTask (const Domain & state, std::istream & input, Task & outputTask)
{
	outputTask.type = Task::Type::PRIMITIVE;

	input >> outputTask.name;
	input >> outputTask.cost;

	// Read number of variables and their sorts
	readMultiple (state, input, outputTask.variableSorts, readPrimitive);

	// Preconditions
	readMultiple (state, input, outputTask.preconditions, readPredicateWithArguments);

	// Add effects
	readMultiple (state, input, outputTask.effectsAdd, readPredicateWithArguments);
	
	// Delete effects
	readMultiple (state, input, outputTask.effectsDel, readPredicateWithArguments);

	// Variable constraints
	readMultiple (state, input, outputTask.variableConstraints, readVariableConstraint);
}

void readAbstractTask (const Domain & state, std::istream & input, Task & outputTask)
{
	outputTask.type = Task::Type::ABSTRACT;

	input >> outputTask.name;
	input >> outputTask.cost;

	// Read variable sorts
	readMultiple (state, input, outputTask.variableSorts, readPrimitive);
}

void readOrderingConstraint (const Domain & state, std::istream & input, std::pair<int, int> & outputOrderingConstraint)
{
	input >> outputOrderingConstraint.first >> outputOrderingConstraint.second;
}

void readDecompositionMethod (const Domain & state, std::istream & input, Domain & outputData)
{
	DecompositionMethod method;

	input >> method.name;

	input >> method.taskNo;
	failIfNotSatisfied (method.taskNo >= 0 && method.taskNo < state.nTotalTasks, "Decomposition method refers to invalid task");
	const Task & taskInfo = state.tasks[method.taskNo];
	Task & task = outputData.tasks[method.taskNo];

	// Read variable sorts
	readMultiple (state, input, method.variableSorts, readPrimitive);

	// Read which variables correspond to the variables of the abstract task
	readN (state, input, method.taskParameters, readPrimitive, taskInfo.variableSorts.size ());

	// Read subtasks
	readMultiple (state, input, method.subtasks, readTaskWithArguments);

	// Ordering constraints
	readMultiple (state, input, method.orderingConstraints, readOrderingConstraint);

	// Variable constraints
	readMultiple (state, input, method.variableConstraints, readVariableConstraint);

	task.decompositionMethods.push_back (method);
}

void parseInput (std::istream & input, Domain & output, Problem & outputProblem)
{
	// Helper alias that we can pass to other functions
	const Domain & state = output;

	// Enable exceptions so we don't have to explicitly check each time we read something
	std::ios::iostate exceptionMask = input.exceptions ();
	input.exceptions (std::ifstream::failbit);

	// Number of constants and sorts
	size_t nConstants;
	size_t nSorts;
	input >> nConstants >> nSorts;

	// Read constant names
	DEBUG (std::cerr << "Reading [" << nConstants << "] constants." << std::endl);
	readN (state, input, output.constants, readPrimitive, nConstants);

	// Read sort names and members
	DEBUG (std::cerr << "Reading [" << nSorts << "] sorts." << std::endl);
	readN (state, input, output.sorts, readSort, nSorts);

	// Read predicates
	readMultiple (state, input, output.predicates, readPredicate);

	// Read number of tasks
	input >> output.nPrimitiveTasks >> output.nAbstractTasks;
	output.nTotalTasks = output.nPrimitiveTasks + output.nAbstractTasks;
	output.tasks.resize (output.nTotalTasks);

	// Read primitive tasks
	DEBUG (std::cerr << "Reading [" << output.nPrimitiveTasks << "] primitive tasks." << std::endl);
	for (int taskIdx = 0; taskIdx < output.nPrimitiveTasks; ++taskIdx)
		readPrimitiveTask (state, input, output.tasks[taskIdx]);

	// Read abstract tasks
	DEBUG (std::cerr << "Reading [" << output.nAbstractTasks << "] abstract tasks." << std::endl);
	for (int taskIdx = output.nPrimitiveTasks; taskIdx < output.nPrimitiveTasks + output.nAbstractTasks; ++taskIdx)
		readAbstractTask (state, input, output.tasks[taskIdx]);

	// Read decomposition methods
	int nMethods;
	input >> nMethods;
	DEBUG (std::cerr << "Reading [" << nMethods << "] decomposition methods." << std::endl);
	for (int methodIdx = 0; methodIdx < nMethods; ++methodIdx)
		readDecompositionMethod (state, input, output);

	// read init + goal facts
	int nInit, nGoal;
	input >> nInit >> nGoal;
	DEBUG (std::cerr << "Reading [" << nInit << "] initial state facts." << std::endl);
	readN (state, input, outputProblem.init, readFact , nInit);

	DEBUG (std::cerr << "Reading [" << nGoal << "] goal facts." << std::endl);
	readN (state, input, outputProblem.goal, readFact , nGoal);

	// read initial task
	input >> outputProblem.initialAbstractTask;

	// Reset exception mask
	input.exceptions (exceptionMask);
}

bool readInput (std::istream & is, Domain & output, Problem & outputProblem)
{
	// Read the entire stream and remove comments
	std::stringstream dataStream;
	std::string line;
	while (std::getline (is, line))
	{
		// Ignore comments
		if (line.size () > 0 && line[0] == '#')
			continue;

		dataStream << line << "\n";
	}

	try
	{
		parseInput (dataStream, output, outputProblem);
	}
	catch (std::ifstream::failure & e)
	{
		std::cerr << "Input parse error: " << e.what () << std::endl;

		if (dataStream.eof ())
		{
			std::cerr << "Reached EOF while reading input." << std::endl;
		}
		else
		{
			// Clear errors so we can read the failing line
			dataStream.clear ();
			std::string errLine;
			if (getline (dataStream, errLine))
				std::cerr << "The error is at: " << errLine << std::endl;
			else
				std::cerr << "Unable to get erroneous line." << std::endl;
		}
		return false;
	}

	return true;
}
