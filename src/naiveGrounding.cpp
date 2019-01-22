#include "naiveGrounding.h"

#include <iostream>
#include <map>
#include <set>

using namespace std;


struct TaskGroundInstance{
	int task;
	vector<int> args;
	
	vector<int> pre,add,del;
};

struct GroundFact{
	int pred;
	vector<int> args;

};

struct MethodGroundInstance{
	int task;
	int method;
	vector<int> args;

	int at;
	vector<int> subtasks;
};


bool operator <(const GroundFact& x, const GroundFact& y) {
	if (x.pred < y.pred) return true;
	if (x.pred > y.pred) return false;

	if (x.args < y.args) return true;
	return false;
}

bool operator <(const TaskGroundInstance& x, const TaskGroundInstance& y) {
	if (x.task < y.task) return true;
	if (x.task > y.task) return false;

	if (x.args < y.args) return true;
	return false;
}

vector<TaskGroundInstance> naivelyGroundTask(Domain & domain, int task, int vPos){
	if (vPos == int(domain.tasks[task].variableSorts.size())){
		TaskGroundInstance inst;
		inst.task = task;
		vector<TaskGroundInstance> ret;
		ret.push_back(inst);
		return ret;
	}

	// get instances of next layer
	vector<TaskGroundInstance> nextG = naivelyGroundTask (domain, task, vPos+1);

	// iterate through constants for that variable
	int vSort = domain.tasks[task].variableSorts[vPos];
	vector<TaskGroundInstance> ret;
	for (unsigned int inSortIndex = 0; inSortIndex < domain.sorts[vSort].members.size(); inSortIndex++){
		int c = domain.sorts[vSort].members[inSortIndex];
		for (unsigned int og = 0; og < nextG.size(); og++){
			TaskGroundInstance inst;
			inst.task = task;
			inst.args.push_back(c);
			for (unsigned int arg = 0; arg < nextG[og].args.size(); arg++)
				inst.args.push_back(nextG[og].args[arg]);
			
			// if we are root check constraint consistency
			if (vPos == 0){
				bool failed = false;
				for (unsigned constr = 0; constr < domain.tasks[task].variableConstraints.size(); constr++){
					VariableConstraint con = domain.tasks[task].variableConstraints[constr];
					int c1 = inst.args[con.var1];
					int c2 = inst.args[con.var2];
					if (con.type == VariableConstraint::Type::EQUAL && c1 != c2) failed = true;
					if (con.type == VariableConstraint::Type::NOT_EQUAL && c1 == c2) failed = true;
				}
				if (failed) continue;
			
			}
			ret.push_back(inst);
		}
	}
	return ret;
}



vector<MethodGroundInstance> naivelyGroundMethod(Domain & domain, int at, int method, int vPos){
	if (vPos == int(domain.tasks[at].decompositionMethods[method].variableSorts.size())){
		MethodGroundInstance inst;
		inst.task = at;
		inst.method = method;
		vector<MethodGroundInstance> ret;
		ret.push_back(inst);
		return ret;
	}

	// get instances of next layer
	vector<MethodGroundInstance> nextG = naivelyGroundMethod (domain, at, method, vPos+1);

	// iterate through constants for that variable
	int vSort = domain.tasks[at].decompositionMethods[method].variableSorts[vPos];
	vector<MethodGroundInstance> ret;
	for (unsigned int inSortIndex = 0; inSortIndex < domain.sorts[vSort].members.size(); inSortIndex++){
		int c = domain.sorts[vSort].members[inSortIndex];
		for (unsigned int og = 0; og < nextG.size(); og++){
			MethodGroundInstance inst;
			inst.task = at;
			inst.method = method;
			inst.args.push_back(c);
			for (unsigned int arg = 0; arg < nextG[og].args.size(); arg++)
				inst.args.push_back(nextG[og].args[arg]);
			
			// if we are root check constraint consistency
			if (vPos == 0){
				bool failed = false;
				for (unsigned constr = 0; constr < domain.tasks[at].decompositionMethods[method].variableConstraints.size(); constr++){
					VariableConstraint con = domain.tasks[at].decompositionMethods[method].variableConstraints[constr];
					int c1 = inst.args[con.var1];
					int c2 = inst.args[con.var2];
					if (con.type == VariableConstraint::Type::EQUAL && c1 != c2) failed = true;
					if (con.type == VariableConstraint::Type::NOT_EQUAL && c1 == c2) failed = true;
				}
				if (failed) continue;
			
			}
			ret.push_back(inst);
		}
	}

	return ret;
}


int numForFact(map<GroundFact,int> & fti, Domain & domain, TaskGroundInstance & gt, PredicateWithArguments & arg){
	GroundFact gf;
	gf.pred = arg.predicateNo;
	for (unsigned int argc = 0;  argc < arg.arguments.size(); argc++)
		gf.args.push_back(gt.args[arg.arguments[argc]]);
  
	if (!fti.count(gf)) fti[gf] = fti.size();
	return fti[gf];
}



void naiveGrounding(Domain & domain, Problem & problem){
	// 1. fully instantiate all primitive tasks
	vector<TaskGroundInstance> allInst;
	
	map<TaskGroundInstance,int> tti;
	for (int t = 0; t < domain.nPrimitiveTasks; t++){
		vector<TaskGroundInstance> gs = naivelyGroundTask(domain,t,0);
		for (unsigned int g = 0; g < gs.size(); g++)
			allInst.push_back(gs[g]), tti[gs[g]] = tti.size();
	}
	cout << allInst.size() << endl;


	map<GroundFact,int> fti;
	// compute all ground facts
	for (int gt = 0; gt < int(allInst.size()); gt++){
		for (int pre = 0; pre < int(domain.tasks[allInst[gt].task].preconditions.size()); pre++)
			allInst[gt].pre.push_back(numForFact(fti, domain, allInst[gt], domain.tasks[allInst[gt].task].preconditions[pre]));
		for (int add = 0; add < int(domain.tasks[allInst[gt].task].effectsAdd.size()); add++)
			allInst[gt].add.push_back(numForFact(fti, domain, allInst[gt], domain.tasks[allInst[gt].task].effectsAdd[add]));
		for (int del = 0; del < int(domain.tasks[allInst[gt].task].effectsDel.size()); del++)
			allInst[gt].del.push_back(numForFact(fti, domain, allInst[gt], domain.tasks[allInst[gt].task].effectsDel[del]));
	}



	// and translate the initial state
	set<int> state;
	for (unsigned int init = 0; init < problem.init.size(); init++){
		GroundFact gf;
		gf.pred = problem.init[init].predicateNo;
		gf.args = problem.init[init].arguments;
		
		if (!fti.count(gf)) fti[gf] = fti.size();

		state.insert(fti[gf]);
		/*cout << "INIT " << fti[gf];
		cout << " " << domain.predicates[gf.pred].name;
		for (int a : gf.args) cout << " " << domain.constants[a];
		cout << endl;*/
	}



	// run PG in very slow time
	vector<bool> appli (int(allInst.size()));
	for (int gt = 0; gt < int(allInst.size()); gt++) appli[gt] = false; 
	int cappli = 0;

	bool changed = true;
	while (changed){
		changed = false;
		// go over all gts
		for (int gt = 0; gt < int(allInst.size()); gt++){
			if (appli[gt]) continue;
			// check prec
			bool all = true;
			for (int p : allInst[gt].pre) all &= state.count(p) != 0;
			if (!all) continue;
			
			appli[gt] = true;
			cappli++;
			for (int p : allInst[gt].add){
				if (state.count(p)) continue;
				changed = true;
				state.insert(p);
			}
		}
	}

	cout << cappli << " " << state.size() << endl;
	/*for (int gt = 0; gt < int(allInst.size()); gt++){
		if (!appli[gt]) continue;
		//if (appli[gt]) cout << "!  ";
		cout << domain.tasks[allInst[gt].task].name;
		for (unsigned int arg = 0; arg < allInst[gt].args.size(); arg++)
			cout << " " << domain.constants[allInst[gt].args[arg]];
		
		//for (int pp : allInst[gt].pre) cout << " " << pp;
		//for (int pp : allInst[gt].add) cout << " +" << pp;

		cout << endl;
	}


	for (auto e : fti){
		if (!state.count(e.second)) continue;
		cout << domain.predicates[e.first.pred].name;
		for (int a : e.first.args) cout << " " << domain.constants[a];
		cout << endl;
	}*/	


	// 2. Instantiate all abstract tasks
	vector<TaskGroundInstance> allAT;
	for (int t = domain.nPrimitiveTasks; t < domain.nPrimitiveTasks + domain.nAbstractTasks; t++){
		vector<TaskGroundInstance> gs = naivelyGroundTask(domain,t,0);
		for (unsigned int g = 0; g < gs.size(); g++)
			allAT.push_back(gs[g]), tti[gs[g]] = tti.size(); 
	}
	cout << "AT groundings: " << allAT.size() << endl;

	// instantiate all methods
	vector<MethodGroundInstance> allM;
	for (int t = domain.nPrimitiveTasks; t < domain.nPrimitiveTasks + domain.nAbstractTasks; t++){
		for (int m = 0; m < int(domain.tasks[t].decompositionMethods.size()); m++){
			vector<MethodGroundInstance> gs = naivelyGroundMethod(domain,t,m,0);
			for (unsigned int g = 0; g < gs.size(); g++)
				allM.push_back(gs[g]);
		}
	}
	cout << "Method groundings: " << allM.size() << endl;



	// add task ids to every method instance
	for (int gm = 0; gm < int(allM.size()); gm++){
		DecompositionMethod m = domain.tasks[allM[gm].task].decompositionMethods[allM[gm].method];
		TaskGroundInstance atg;
		atg.task = m.taskNo;
		for (int a = 0; a < int(m.taskParameters.size()); a++)
			atg.args.push_back(allM[gm].args[m.taskParameters[a]]);
		allM[gm].at = tti[atg];
		
		for (int s = 0; s < int(m.subtasks.size()); s++){
			TaskGroundInstance stg;
			stg.task = m.subtasks[s].taskNo;
			for (int a = 0; a < int(m.subtasks[s].arguments.size()); a++)
				stg.args.push_back(allM[gm].args[m.subtasks[s].arguments[a]]);
			allM[gm].subtasks.push_back(tti[stg]);
		}
	}
	
	// run bottom up reachability
	vector<bool> aappli (int(allAT.size()));
	vector<bool> mappli (int(allM.size()));
	changed = true;
	while(changed){
		changed = false;
		for (int gm = 0; gm < int(allM.size()); gm++){
			bool allOK = true;
			for (unsigned int st = 0; st < allM[gm].subtasks.size(); st++)
				if (allM[gm].subtasks[st] < int(allInst.size())) allOK &= appli[allM[gm].subtasks[st]];
				else allOK &= aappli[allM[gm].subtasks[st] - allInst.size()];
			if (!allOK) continue;
			mappli[gm] = true;
			if (aappli[allM[gm].at - allInst.size()]) continue;
			aappli[allM[gm].at - allInst.size()] = true;
			changed = true;
		}
	}


	for (int gt = 0; gt < int(allAT.size()); gt++){
		if (!aappli[gt]) continue;
		cout << domain.tasks[allAT[gt].task].name;
		for (unsigned int arg = 0; arg < allAT[gt].args.size(); arg++)
			cout << " " << domain.constants[allAT[gt].args[arg]];
		cout << endl;
	}

	for (int gm = 0; gm < int(allM.size()); gm++){
		if (!mappli[gm]) continue;
		DecompositionMethod m = domain.tasks[allM[gm].task].decompositionMethods[allM[gm].method];
		cout << m.name;
		for (unsigned int arg = 0; arg < allM[gm].args.size(); arg++)
			cout << " " << domain.constants[allM[gm].args[arg]];
		cout << ": " << allM[gm].at << " ->";
		for (unsigned int st = 0; st < allM[gm].subtasks.size(); st++)
			cout << " " << allM[gm].subtasks[st];
		
		cout << endl;
	}

	return;
}
