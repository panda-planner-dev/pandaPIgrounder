#ifndef MODEL_H_INCLUDED
#define MODEL_H_INCLUDED

/**
 * @defgroup model Input Model
 * @brief Contains data structures for representing problem domains.
 *
 * @{
 */

#include <map>
#include <set>
#include <string>
#include <vector>
#include <variant>


/**
 * @brief Sort (aka type) of a variable.
 */
struct Sort
{
	/// The name of the sort.
	std::string name;

	/// Vector of members of this sort. Every element of this vector is the index of a constant in the Domain.constants vector.
	std::set<int> members;
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

	/// marks a predicate as artificial for conditional effects
	bool guard_for_conditional_effect;

};

/**
 * @brief TODO
 */
template <typename T>
concept bool Literal = requires (T instance, int headNo)
{
	{ instance.setHeadNo (headNo) } -> void;
	{ instance.getHeadNo () } -> int;
	{ instance.arguments } -> std::vector<int>;
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

	void setHeadNo (int headNo);

	int getHeadNo (void) const;
};

/**
 * @brief A fact is a predicate with constants assigned to the predicate's arguments.
 */
struct Fact
{
	/// The number of this fact.
	int groundedNo = -1;

	/// Number of this fact in an output
	int outputNo = -1;

	/// The index of the predicate in the Domain.predicates vector.
	int predicateNo;

	/// Vector of arguments. This means that the i-th argument to this predicate is the arguments[i]-th constant from the Domain.constants vector.
	std::vector<int> arguments;

	void setHeadNo (int headNo);

	int getHeadNo (void) const;

	bool operator < (const Fact & other) const;

	bool operator == (const Fact & other) const;
};

/// hash function s.t. facts can be put into unordered sets
namespace std {
    template<> struct hash<Fact>
    {
        std::size_t operator()(const Fact& f) const noexcept
        {
			std::size_t h = f.predicateNo;
			for (const int & a : f.arguments) h = h*601 + a;

			return h;
        }
    };
}


/**
 * @brief A task where a method's variables are used as arguments to the task.
 */
struct TaskWithArguments
{
	/// The index of the task in the Domain.tasks vector.
	int taskNo;

	/// Vector of arguments. This means that the i-th argument to this task is the arguments[i]-th variable for this decomposition method.
	std::vector<int> arguments;

	void setHeadNo (int headNo);

	int getHeadNo (void) const;
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

namespace pandaPI{


/**
 * @brief ???
 */
template<typename OperationType>
struct Operator
{
	/// Name of the operator.
	std::string name;

	/// The sorts of this task's variables. Use `variableSorts.size ()` to get the number of variables.
	/// Vector of variable sorts. This means that this method's i-th variable has the sort variableSorts[i].
	std::vector<int> variableSorts;

	/// Variable constraints
	std::vector<VariableConstraint> variableConstraints;

	// Force subclasses to implement the getAntecedents() method
	const std::vector<OperationType> & getAntecedents (void);

	// Force subclasses to implement the getConsequences() method
	const std::vector<OperationType> & getConsequences (void);

protected:
	Operator (void) {};
};

}

/**
 * @brief A method that an abstract task can be decomposed to.
 */
struct DecompositionMethod : pandaPI::Operator<TaskWithArguments>
{
	/// The index of the abstract task in the Domain.tasks vector that this method belongs to.
	int taskNo;

	/// Abstract task parameters.
	std::vector<int> taskParameters;

	/// Subtasks
	std::vector<TaskWithArguments> subtasks;

	/// Subtask ordering constraints
	std::vector<std::pair<int, int>> orderingConstraints;

	const std::vector<TaskWithArguments> & getAntecedents (void) const;

	const std::vector<TaskWithArguments> getConsequences (void) const;

	DecompositionMethod (void) {};
};

// forward declaration
struct GroundedTask;


/**
 * @brief A task with variables, and optional preconditions and delete/add effects.
 */
struct Task: pandaPI::Operator<PredicateWithArguments>
{
	
	enum Type
	{
		PRIMITIVE,
		ABSTRACT,
	} type; ///< The type of this task. Either Type::PRIMITIVE or Type::ABSTRACT.

	int number_of_original_variables;

	/// if true, this is an artificial task representing a conditional effect
	bool isCompiledConditionalEffect;

	/// The cost to execute this task.
	std::vector<std::variant<PredicateWithArguments,int>> costs;

	/// Preconditions that must be fulfilled to execute this task.
	std::vector<PredicateWithArguments> preconditions;

	/// Predicates that will be deleted when this task is executed.
	std::vector<PredicateWithArguments> effectsDel;

	/// Predicates that will be added when this task is executed.
	std::vector<PredicateWithArguments> effectsAdd;

	/// Conditional Add effects. Will be added to the state if their condition is satisfied
	std::vector<std::pair<std::vector<PredicateWithArguments>, PredicateWithArguments>> conditionalAdd;
	
	/// Conditional Del effects. Will be removed from the state if their condition is satisfied
	std::vector<std::pair<std::vector<PredicateWithArguments>, PredicateWithArguments>> conditionalDel;

	/// Decomposition methods for abstract tasks. Each element is an index into the Domain.decompositionMethods vector.
	std::vector<int> decompositionMethods;

	const std::vector<PredicateWithArguments> & getAntecedents (void) const;

	const std::vector<PredicateWithArguments> & getConsequences (void) const;

	/**
	 * @brief Check whether the given Fact fulfils the given precondition.
	 *
	 * This will also check whether the fact arguments match the task's variable sorts.
	 *
	 * If a VariableAssignmentVariableAssignment pointer is given, the variables assigned by using this fact to fulfil this precondition will be returned.
	 */
	bool doesFactFulfilPrecondition (struct VariableAssignment * outputVariableAssignment, const struct Domain & domain, const Fact & fact, int preconditionIdx) const;

	int computeGroundCost(GroundedTask & task,std::map<Fact,int> & init_functions_map) const;
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

	/// Predicate-level mutexes, contains pairs of IDs of predicates for which instances are mutex. Can only involve mutexes of identical arity
	/// These are essentially +/- pairs of predicates 
	std::vector<std::pair<int,int>> predicateMutexes;

	/// Functions
	std::vector<Predicate> functions;

	/// Number of primitive tasks.
	int nPrimitiveTasks;

	/// Number of abstract tasks.
	int nAbstractTasks;

	/// Number of all tasks. Convenience shortcut for (nPrimitiveTasks + nAbstractTasks).
	int nTotalTasks;

	/// All tasks. Primitive tasks have indices in [0; nPrimitiveTasks); abstract tasks have indices in [nPrimitiveTasks; nPrimitiveTasks + nAbstractTasks).
	std::vector<Task> tasks;

	/// Decomposition methods
	std::vector<DecompositionMethod> decompositionMethods;
};

struct Problem
{
	/// List of facts that are known in the initial state.
	std::vector<Fact> init;

	/// List of facts that should be in the goal state. (Not currently processed in any way, but these facts need to be part of the output)
	std::vector<Fact> goal;

	/// List of function value assertions that are true in the initial state
	std::vector<std::pair<Fact,int>> init_functions;

	/// The initial abstract task, identified by its number.
	int initialAbstractTask;
};

/**
 * @brief A structure that stores values assigned to task variables, offering a std::map-like interface.
 *
 * Basically a wrapper for an std::vector with convenience functions for checking whether a variable is assigned or not, and counting the number of assigned variables.
 */
struct VariableAssignment
{
	/// Magic value that marks a variable as not assigned yet.
	constexpr static int NOT_ASSIGNED = -1;

	/**
	 * @brief Vector that stores the variable assignments, indexed by variable index.
	 *
	 * If a variable has the special VariableAssignment::NOT_ASSIGNED value, the variable must be considered to not be assigned yet.
	 */
	std::vector<int> assignments;

	/**
	 * @brief Initializes the VariableAssignment.
	 *
	 * The nVariables argument is the number of supported variables. It is used as the size of the internal assignments vector.
	 *
	 * It is an error to call any other function with an index smaller than 0, or greater than or equal to nVariables.
	 */
	VariableAssignment (size_t nVariables);

	/// Convenience read/write access to an assigned variable.
	int & operator[] (int varIdx);

	/// Convenience read-only access to an assigned variable.
	int operator[] (int varIdx) const;

	/// Assigns a value to a variable.
	void assign (int varIdx, int value);

	/// Returns true if the variable with the given index is assigned.
	bool isAssigned (int varIdx) const;

	/**
	 * @brief Returns the number of assigned variables.
	 *
	 * Has a complexity of O(n), but seems to be fast enough in practice.
	 */
	size_t size (void) const;

	/// Removes the assigned value (if any) for the variable with the given index.
	void erase (int varIdx);

	/// Operator that allows for easy conversion from VariableAssignment to std::vector<int>.
	operator std::vector<int> (void) const;
};

/**
 * @brief Like a std::set<Fact>, but faster!
 *
 * This works by grouping the Facts by their predicate number.
 */
struct FactSet
{
	/// Contains a std::set<Fact> for each predicate.
	std::vector<std::set<Fact>> factsByPredicate;

	/**
	 * @brief Initializes the FactSet.
	 *
	 * The nPredicates argument is the number of supported predicates. It is used as the size of the internal fact set vector.
	 */
	FactSet (size_t nPredicates);

	/**
	 * @brief Returns the number of all facts in the set.
	 *
	 * Has a complexity of O(n) where n is the number of predicates, but seems to be fast enough in practice.
	 */
	size_t size (void) const;

	/**
	 * @brief Returns 1 if the given fact is in the set, or 0 if not.
	 *
	 * It is an error to call this function with a fact where Fact.predicateNo is greater than or equal to nPredicates as passed to the constructor of this FactSet.
	 */
	size_t count (const Fact & fact) const;

	/**
	 * @brief Return the fact in this factset
	 *
	 * It is an error to call this function with a fact where Fact.predicateNo is greater than or equal to nPredicates as passed to the constructor of this FactSet.
	 */
	const Fact & find (const Fact & fact) const;

	/**
	 * @brief Inserts the given fact into the FactSet.
	 *
	 * It is an error to call this function with a fact where Fact.predicateNo is greater than or equal to nPredicates as passed to the constructor of this FactSet.
	 */
	void insert (const Fact & fact);
	
	
	void erase (const Fact & fact);

	/**
	 * @brief Returns the set of facts for the given predicate.
	 *
	 * It is an error to call this function with a predicateNo which is greater than or equal to nPredicates as passed to the constructor of this FactSet.
	 */
	const std::set<Fact> & getFactsForPredicate (int predicateNo) const;

	/// Returns a std::set containing all facts in this FactSet.
	operator std::set<Fact> (void) const;
};

/**
 * @brief A grounded task instance.
 */
struct GroundedTask
{
	/// The number of this grounded task.
	int groundedNo = -1;

	/// Number of this fact in an output
	int outputNo = -1;

	/// outputNos if we compiled cover facts
	std::vector<int> outputNosForCover;

	/// The number of the task that was grounded.
	int taskNo;

	/// The arguments for the grounded task.
	std::vector<int> arguments;

	/// List of grounded decomposition methods (for abstract tasks).
	std::vector<int> groundedDecompositionMethods;

	/// List of grounded preconditions
	std::vector<int> groundedPreconditions;

	/// List of grounded add effects
	std::vector<int> groundedAddEffects;

	/// List of grounded del effects
	std::vector<int> groundedDelEffects;

	/// number of mutex groups for which this action should have the none-of-those effect
	std::vector<int> noneOfThoseEffect;

	void setHeadNo (int headNo);

	int getHeadNo (void) const;

	bool operator < (const GroundedTask & other) const;

	bool operator == (const GroundedTask & other) const;
};

/// hash function s.t. grounded tasks can be put into unordered sets
namespace std {
    template<> struct hash<GroundedTask>
    {
        std::size_t operator()(const GroundedTask& t) const noexcept
        {
			std::size_t h = t.taskNo;
			for (const int & a : t.arguments) h = h*601 + a;

			return h;
        }
    };
}


/**
 * @brief A grounded decomposition method.
 */
struct GroundedMethod
{
	/// The number of this grounded method.
	int groundedNo = -1;

	/// The number of the decomposition method.
	int methodNo;

	/// The arguments for the decomposition method.
	std::vector<int> arguments;

	/// List of grounded preconditions (subtasks)
	std::vector<int> groundedPreconditions;

	/// distinct topological ordering of the subtasks (for output and compliance with verification)
	std::vector<int> preconditionOrdering;

	/// List of grounded add effects (exactly one abstract task)
	std::vector<int> groundedAddEffects;

	void setHeadNo (int headNo);

	int getHeadNo (void) const;

	bool operator < (const GroundedMethod & other) const;

	bool operator == (const GroundedMethod & other) const;
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
