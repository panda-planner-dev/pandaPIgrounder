#include <string>
#include <iostream>
#include <algorithm>

#include "FAMmutexes.h"
#include "pddl/pddl.h"

static const char* root_type_cppdl = "__object_cpddl";
static const char* eq_name_cppdl = "__equals_cpddl";


std::pair<std::vector<int>,std::vector<int>> compute_local_type_hierarchy(const Domain & domain, const Problem & problem){
	// find subset relations between sorts
	
	// [i][j] = true means that j is a subset of i
	std::vector<std::vector<bool>> subset (domain.sorts.size());
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			if (s1 != s2){
				if (std::includes(domain.sorts[s1].members.begin(), domain.sorts[s1].members.end(),
							domain.sorts[s2].members.begin(), domain.sorts[s2].members.end())){
					// here we know that s2 is a subset of s1
					subset[s1].push_back(true);
				} else
					subset[s1].push_back(false);
			} else subset[s1].push_back(false);

	// transitive reduction
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			for (size_t s3 = 0; s3 < domain.sorts.size(); s3++)
				if (subset[s2][s1] && subset[s1][s3])
					subset[s2][s3] = false;
	
	
	/*for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++){
			if (subset[s1][s2]){
				std::cout << domain.sorts[s2].name;
				std::cout << " is a subset of ";
				std::cout << domain.sorts[s1].name;
				std::cout << std::endl;
			
			}
		}
	}*/

	// who is whose direct subset
	std::vector<std::vector<int>> directsubset (domain.sorts.size());
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			if (subset[s1][s2])
				directsubset[s1].push_back(s2);
	
	// determine parents
	std::vector<int> parent (domain.sorts.size());
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		parent[s1] = -1;
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			if (subset[s1][s2]){
				if (parent[s2] != -1){
					std::cerr << "Type hierarchy is not a tree ... cpddl can't handle this. Exiting." << std::endl;
					exit(-1);
				}

				parent[s2] = s1;
			}


	/*for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		std::cout << domain.sorts[s1].name;
   		if (parent[s1] != -1) std::cout << " - " << domain.sorts[parent[s1]].name;
		std::cout << std::endl; 
	}*/

	// assign elements to sorts
	std::vector<std::set<int>> directElements (domain.sorts.size());
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		for (int elem : domain.sorts[s1].members){
			bool in_sub_sort = false;
			for (int s2 : directsubset[s1]){
				if (domain.sorts[s2].members.count(elem)){
					in_sub_sort = true;
					break;
				}
			}
			if (in_sub_sort) continue;
			directElements[s1].insert(elem);
		}
	}
	
	
	/*for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		std::cout << domain.sorts[s1].name << ":";
		for (int e : directElements[s1]) std::cout << " " << domain.constants[e];
		std::cout << std::endl;
	}*/

	std::vector<int> sortOfElement (domain.constants.size());
	for (size_t c = 0; c < domain.constants.size(); c++)
		sortOfElement[c] = -1;
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (int elem : directElements[s1]){
			if (sortOfElement[elem] != -1){
				std::cerr << "Sort is contained in two types .. this cannot happen. Thus must be a bug. Exiting." << std::endl;
				exit(1);
			}
			sortOfElement[elem] = s1;
		}

	return std::make_pair(parent,sortOfElement);	
} 


void topsortTypesCPDDL_dfs(int cur, std::vector<int> & parent,
						   std::vector<bool> & done, std::vector<int> & result){
	if (cur == -1) return;
	if (done[cur]) return;
	done[cur] = true;
	topsortTypesCPDDL_dfs(parent[cur],parent,done,result);
	result.push_back(cur);
}


std::vector<int> topsortTypesCPDDL(std::vector<int> & parent){
	std::vector<bool> done (parent.size());
	for (size_t i = 0; i < done.size(); i++) done[i] = false;

	std::vector<int> result;
	for (size_t i = 0; i < done.size(); i++)
		if (!done[i])
			topsortTypesCPDDL_dfs(i,parent,done,result);

	return result;
}


/////////////////////////////////// COPIED FROM CPDDL/src/obj.c
struct obj_key {
    pddl_obj_id_t obj_id;
    const char *name;
    uint32_t hash;
    bor_list_t htable;
};
typedef struct obj_key obj_key_t;

static bor_htable_key_t objHash(const bor_list_t *key, void *_)
{
    const obj_key_t *obj = bor_container_of(key, obj_key_t, htable);
    return obj->hash;
}

static int objEq(const bor_list_t *key1, const bor_list_t *key2, void *_)
{
    const obj_key_t *obj1 = bor_container_of(key1, obj_key_t, htable);
    const obj_key_t *obj2 = bor_container_of(key2, obj_key_t, htable);
    return strcmp(obj1->name, obj2->name) == 0;
}

static void addEqPredicate(pddl_preds_t *ps)
{
    pddl_pred_t *p;

    p = pddlPredsAdd(ps);
    p->name = BOR_STRDUP(eq_name_cppdl);
    p->param_size = 2;
    p->param = BOR_CALLOC_ARR(int, 2);
    ps->eq_pred = ps->pred_size - 1;
}
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c

/////////////////////////////////// COPIED FROM CPDDL/src/cond.c
#define condNew(CTYPE, TYPE) \
    (CTYPE *)_condNew(sizeof(CTYPE), TYPE)

static pddl_cond_t *_condNew(int size, unsigned type)
{
    pddl_cond_t *c;

    c = (pddl_cond_t*)BOR_MALLOC(size);
    bzero(c, size);
    c->type = type;
    borListInit(&c->conn);
    return c;
}

static pddl_cond_part_t *condPartNew(int type)
{
    pddl_cond_part_t *p;
    p = condNew(pddl_cond_part_t, type);
    borListInit(&p->part);
    return p;
}

static pddl_cond_atom_t *condAtomNew(void)
{
    return condNew(pddl_cond_atom_t, PDDL_COND_ATOM);
}

static void condPartAdd(pddl_cond_part_t *p, pddl_cond_t *add)
{
    borListInit(&add->conn);
    borListAppend(&p->part, &add->conn);
}

/////////////////////////////////// COPIED FROM CPDDL/src/cond.c



void compute_FAM_mutexes(const Domain & domain, const Problem & problem, bool quietMode){
	// create representation of the domain/problem
	pddl_t pddl;
	bzero(&pddl,sizeof(pddl_t));
	std::string name = "dom";
	pddl.domain_name = const_cast<char*>(name.c_str());
	std::string name2 = "prob";
	pddl.problem_name = const_cast<char*>(name2.c_str());
	pddl.require = PDDL_REQUIRE_TYPING + PDDL_REQUIRE_CONDITIONAL_EFF;
	
	// compute a local type hierarchy
	auto [typeParents,objectType] = compute_local_type_hierarchy(domain,problem);
	
	// cpddl needs a root type named object
	pddlTypesAdd(&pddl.type,root_type_cppdl,-1);
	
	for (int sort : topsortTypesCPDDL(typeParents))
			// +1 is for the artificial root sort
		pddlTypesAdd(&pddl.type,domain.sorts[sort].name.c_str(),typeParents[sort]+1);
	
	std::cout << "Types added " << std::endl;
	bzero(&pddl.obj, sizeof(pddl.obj));
	pddl.obj.htable = borHTableNew(objHash, objEq, NULL);
	
	// add objects
	for (size_t o = 0; o < domain.constants.size(); o++){
		pddl_obj_t * obj = pddlObjsAdd(&pddl.obj,domain.constants[o].c_str());
		obj->type = objectType[o] + 1; // +1 for root sort
		obj->is_constant = true;
		obj->is_private = 0;
		obj->owner = PDDL_OBJ_ID_UNDEF;
		obj->is_agent = 0;
	}
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c
    for (int i = 0; i < pddl.obj.obj_size; ++i){
        pddlTypesAddObj(&pddl.type, i, pddl.obj.obj[i].type);
	}
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c

	// add equals predicate
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c
    pddl.pred.eq_pred = -1;
    addEqPredicate(&pddl.pred);
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c

	for (const Predicate & pred : domain.predicates){
		pddl_pred_t * p = pddlPredsAdd(&pddl.pred);
		p->name = BOR_STRDUP(pred.name.c_str());
		p->param_size = pred.argumentSorts.size();
    	p->param = BOR_REALLOC_ARR(p->param, int, p->param_size);
        for (size_t i = 0; i < pred.argumentSorts.size(); i++)
			p->param[i] = pred.argumentSorts[i] + 1; // +1 for __object
	}

	// add dummy predicate to avoid pruning
	{
		pddl_pred_t * p = pddlPredsAdd(&pddl.pred);
		p->name = BOR_STRDUP("dummy-goal");
		p->param_size = 0;
   		p->param = BOR_REALLOC_ARR(p->param, int, p->param_size);
	}

	// add actions to the model
	for (size_t tid = 0; tid < domain.nPrimitiveTasks; tid++){
		const Task & t = domain.tasks[tid];
    	pddl_action_t *a;
    	a = pddlActionsAddEmpty(&pddl.action);
		a->name = BOR_STRDUP(t.name.c_str());

		int varidx = 0;
		for (const int & parameter : t.variableSorts){
			pddl_param_t * p = pddlParamsAdd(&(a->param));
			std::string paramName = "?var" + std::to_string(varidx++);
			p->name = BOR_STRDUP(paramName.c_str());
			p->type = parameter + 1; // +1 for object
			p->is_agent = 0;
		}

		// TODO other handling of empty preconditions ...
		
		if (t.preconditions.size() + t.variableConstraints.size() == 0){
			a->pre = pddlCondNewEmptyAnd();
		} else {
			// add preconditions
			pddl_cond_part_t * pre_conj = condPartNew(PDDL_COND_AND);
			for (const PredicateWithArguments & pre : t.preconditions){
				pddl_cond_atom_t * atom = condAtomNew();
				atom->pred = pre.predicateNo + 1; // +1 for equals
				atom->arg_size = pre.arguments.size();
		    	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
				atom->neg = false;
				for (size_t i = 0; i < pre.arguments.size(); i++){
					atom->arg[i].param = pre.arguments[i];
					atom->arg[i].obj = PDDL_OBJ_ID_UNDEF;
				}
				condPartAdd(pre_conj,&atom->cls);
			}
			
			// add the variable constraints
			for (const VariableConstraint & vc : t.variableConstraints){
				pddl_cond_atom_t * atom = condAtomNew();
				atom->pred = 0; // equals
				atom->arg_size = 2;
		    	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
				atom->neg = vc.type == VariableConstraint::Type::NOT_EQUAL;

				atom->arg[0].param = vc.var1;
				atom->arg[1].param = vc.var1;
				atom->arg[0].obj = PDDL_OBJ_ID_UNDEF;
				atom->arg[1].obj = PDDL_OBJ_ID_UNDEF;

				condPartAdd(pre_conj,&atom->cls);
			}
			
			
			a->pre = &(pre_conj->cls);
		}



		// add effect
		pddl_cond_part_t * eff_conj = condPartNew(PDDL_COND_AND);
		std::vector<std::pair<bool,PredicateWithArguments>> normal_eff;
		for (auto & add : t.effectsAdd)
			normal_eff.push_back(std::make_pair(true,add));
		for (auto & del : t.effectsDel)
			normal_eff.push_back(std::make_pair(false,del));

		{ // artificial goal predicate
			pddl_cond_atom_t * atom = condAtomNew();
			atom->pred = domain.predicates.size() + 1;
			atom->arg_size = 0;
	    	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
			atom->neg = false;
			condPartAdd(eff_conj,&atom->cls);
		}


		for (auto & eff : normal_eff){
			pddl_cond_atom_t * atom = condAtomNew();
			atom->pred = eff.second.predicateNo + 1; // +1 for equals
			atom->arg_size = eff.second.arguments.size();
	    	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
			atom->neg = !eff.first;
			for (size_t i = 0; i < eff.second.arguments.size(); i++){
				atom->arg[i].param = eff.second.arguments[i];
				atom->arg[i].obj = PDDL_OBJ_ID_UNDEF;
			}
			condPartAdd(eff_conj,&atom->cls);
		}
		
		
		
		std::vector<std::pair<bool,std::pair<std::vector<PredicateWithArguments>, PredicateWithArguments>>> cond_eff;
		for (auto & add : t.conditionalAdd)
			cond_eff.push_back(std::make_pair(true,add));
		for (auto & del : t.conditionalDel)
			cond_eff.push_back(std::make_pair(false,del));


		for (auto & eff : cond_eff){
			pddl_cond_when_t * w = condNew(pddl_cond_when_t, PDDL_COND_WHEN);

			// build precondition of CE
			pddl_cond_part_t * pre_conj = condPartNew(PDDL_COND_AND);
			for (const PredicateWithArguments & pre : eff.second.first){
				pddl_cond_atom_t * atom = condAtomNew();
				atom->pred = pre.predicateNo + 1; // +1 for equals
				atom->arg_size = pre.arguments.size();
		    	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
				atom->neg = false;
				for (size_t i = 0; i < pre.arguments.size(); i++){
					atom->arg[i].param = pre.arguments[i];
					atom->arg[i].obj = PDDL_OBJ_ID_UNDEF;
				}
				condPartAdd(pre_conj,&atom->cls);
			}
			w->pre = &pre_conj->cls;


			// build conditional effect
			pddl_cond_atom_t * eff_atom = condAtomNew();
			eff_atom->pred = eff.second.second.predicateNo + 1; // +1 for equals
			eff_atom->arg_size = eff.second.second.arguments.size();
	    	eff_atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, eff_atom->arg_size);
			eff_atom->neg = !eff.first;
			for (size_t i = 0; i < eff.second.second.arguments.size(); i++){
				eff_atom->arg[i].param = eff.second.second.arguments[i];
				eff_atom->arg[i].obj = PDDL_OBJ_ID_UNDEF;
			}

			w->eff = &eff_atom->cls;
			condPartAdd(eff_conj,&w->cls);
		}

		a->eff = &(eff_conj->cls);
	}





	//// PROBLEM DEFINITION

	// init
	pddl.init = condPartNew(PDDL_COND_AND);
	for (const Fact & f : problem.init){
		pddl_cond_atom_t * atom = condAtomNew();
		atom->pred = f.predicateNo + 1; // +1 for equals
		atom->arg_size = f.arguments.size();
    	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
		atom->neg = false;
		for (size_t i = 0; i < f.arguments.size(); i++){
			atom->arg[i].param = -1;
			atom->arg[i].obj = pddlObjsGet(&pddl.obj, domain.constants[f.arguments[i]].c_str()); 
		}
		condPartAdd(pddl.init,&atom->cls);
	}


	// goal
	pddl_cond_part_t * goal = condPartNew(PDDL_COND_AND);
	{ // artificial goal predicate
		pddl_cond_atom_t * atom = condAtomNew();
		atom->pred = domain.predicates.size() + 1;
		atom->arg_size = 0;
    	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
		atom->neg = false;
		condPartAdd(goal,&atom->cls);
	}
	for (const Fact & f : problem.goal){
		pddl_cond_atom_t * atom = condAtomNew();
		atom->pred = f.predicateNo + 1; // +1 for equals
		atom->arg_size = f.arguments.size();
    	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
		atom->neg = false;
		for (size_t i = 0; i < f.arguments.size(); i++){
			atom->arg[i].param = -1;
			atom->arg[i].obj = pddlObjsGet(&pddl.obj, domain.constants[f.arguments[i]].c_str()); 
		}
		condPartAdd(goal,&atom->cls);
	}
	pddl.goal = &(goal->cls);

	pddlTypesBuildObjTypeMap(&pddl.type, pddl.obj.obj_size);

	
	pddlPrintPDDLDomain(&pddl,stdout);
	pddlPrintPDDLProblem(&pddl,stdout);

	//////////////////// Mutex computation
	pddlNormalize(&pddl);

	pddlPrintPDDLDomain(&pddl,stdout);
	pddlPrintPDDLProblem(&pddl,stdout);


	exit(0);
	pddl_lifted_mgroups_infer_limits_t limits = PDDL_LIFTED_MGROUPS_INFER_LIMITS_INIT;
	limits.max_candidates = 10000; //o.max_candidates;
	limits.max_mgroups = 10000; //o.max_mgroups;
	pddl_lifted_mgroups_t lifted_mgroups;
	pddl_lifted_mgroups_t monotonicity_invariants;
	pddlLiftedMGroupsInit(&lifted_mgroups);
	pddlLiftedMGroupsInit(&monotonicity_invariants);
	bor_err_t err = BOR_ERR_INIT;
	pddlLiftedMGroupsInferFAMGroups(&pddl, &limits, &lifted_mgroups, &err);

	std::cout << "LG " << lifted_mgroups.mgroup_size << std::endl;
	std::cout << "MON " << monotonicity_invariants.mgroup_size << std::endl;

    for (int li = 0; li < lifted_mgroups.mgroup_size; ++li){
        fprintf(stdout, "M:%d: ", li);
        pddlLiftedMGroupPrint(&pddl, lifted_mgroups.mgroup + li, stdout);
    }

    for (int li = 0; li < monotonicity_invariants.mgroup_size; ++li){
        const pddl_lifted_mgroup_t *m = monotonicity_invariants.mgroup + li;
        fprintf(stdout, "I:%d: ", li);
        pddlLiftedMGroupPrint(&pddl, m, stdout);
    }




	exit(-1);
}

