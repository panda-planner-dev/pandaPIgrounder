#ifndef MODEL_H_INCLUDED
#define MODEL_H_INCLUDED

/**
 * @defgroup model Input Model
 * @brief Contains data structures for representing problem domains.
 *
 * @{
 */

#include <string>
#include <vector>

/**
 * @brief Sort (aka type) of a variable.
 */
struct Sort
{
	/// The name of the sort.
	std::string name;

	/// Vector of members of this sort. Every element of this vector is the index of a constant in the Domain.constants vector.
	std::vector<int> members;
};

/**
 * @brief A predicate with parameters.
 */
struct Predicate
{
	/// The name of the predicate.
	std::string name;

	/// Vector of argument sorts. The i-th argument to this predicate has to be of sort argumentSorts[i].
	std::vector<int> argumentSorts;
};

/**
 * @brief A predicate where a task's variables are used as arguments to the predicate.
 */
struct PredicateWithArguments
{
	/// The index of the predicate in the Domain.predicates vector.
	int predicateNo;

	/// Vector of arguments. This means that the i-th argument to this predicate is the arguments[i]-th variable for this task.
	std::vector<int> arguments;
};

/**
 * @brief A task where a method's variables are used as arguments to the task.
 */
struct TaskWithArguments
{
	/// The index of the task in the Domain.tasks vector.
	int taskNo;

	/// Vector of arguments. This means that the i-th argument to this task is the arguments[i]-th variable for this decomposition method.
	std::vector<int> arguments;
};

/**
 * @brief A constraint on two variables for a task.
 */
struct VariableConstraint
{
	enum Type
	{
		/// The two variables referenced in this constraint must be equal.
		EQUAL,

		/// The two variables referenced in this constraint must NOT be equal.
		NOT_EQUAL,
	} type; ///< The type of this constraint.

	/// The first variable.
	int var1;

	/// The second variable.
	int var2;
};

/**
 * @brief A method that an abstract task can be decomposed to.
 */
struct DecompositionMethod
{
	/// Name of the method.
	std::string name;

	/// The index of the abstract task in the Domain.tasks vector that this method belongs to.
	int taskNo;

	/// Vector of variable sorts. This means that this method's i-th variable has the sort variableSorts[i].
	std::vector<int> variableSorts;

	/// Abstract task parameters.
	std::vector<int> taskParameters;

	/// Subtasks
	std::vector<TaskWithArguments> subtasks;

	/// Subtask ordering constraints
	std::vector<std::pair<int, int>> orderingConstraints;

	/// Variable constraints
	std::vector<VariableConstraint> variableConstraints;
};

/**
 * @brief A task with variables, and optional preconditions and delete/add effects.
 */
struct Task
{
	enum Type
	{
		PRIMITIVE,
		ABSTRACT,
	} type; ///< The type of this task. Either Type::PRIMITIVE or Type::ABSTRACT.

	/// The name of this task.
	std::string name;

	/// The cost to execute this task.
	int cost;

	/// The sorts of this task's variables. Use `variableSorts.size ()` to get the number of variables.
	std::vector<int> variableSorts;

	/// Preconditions that must be fulfilled to execute this task.
	std::vector<PredicateWithArguments> preconditions;

	/// Predicates that will be deleted when this task is executed.
	std::vector<PredicateWithArguments> effectsDel;

	/// Predicates that will be added when this task is executed.
	std::vector<PredicateWithArguments> effectsAdd;

	/// Variable constraints
	std::vector<VariableConstraint> variableConstraints;

	/// Decomposition methods for abstract tasks
	std::vector<DecompositionMethod> decompositionMethods;
};

/**
 * @brief A planning domain.
 */
struct Domain
{
	/// Constants
	std::vector<std::string> constants;

	/// Sorts
	std::vector<Sort> sorts;

	/// Predicates
	std::vector<Predicate> predicates;

	/// Number of primitive tasks.
	int nPrimitiveTasks;

	/// Number of abstract tasks.
	int nAbstractTasks;

	/// Number of all tasks. Convenience shortcut for (nPrimitiveTasks + nAbstractTasks).
	int nTotalTasks;

	/// All tasks. Primitive tasks have indices in [0; nPrimitiveTasks); abstract tasks have indices in [nPrimitiveTasks; nPrimitiveTasks + nAbstractTasks).
	std::vector<Task> tasks;
};

struct Fact
{
	/// The index of the predicate in the Domain.predicates vector.
	int predicateNo;

	/// Vector of arguments. This means that the i-th argument to this predicate is the arguments[i]th constant in the domain.
	std::vector<int> arguments;
};

struct Problem
{
	/// The initial state
	std::vector<Fact> init;

	/// The goal state
	std::vector<Fact> goal;

	/// the initial abstract task, identified by its number
	int initialAbstractTask;
};


struct BadInputException : public std::exception
{
	std::string message;

	BadInputException (std::string message);

	const char * what () const throw () override;
};

/**
 * @}
 */

#endif
