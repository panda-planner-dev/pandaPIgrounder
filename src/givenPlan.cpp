#include "givenPlan.h"
#include "debug.h"

#include <fstream>
#include <iostream>
#include <vector>
#include <set>
#include <unordered_map>
#include <algorithm>
#include <sstream>

given_plan_typing_information extract_given_plan_typer(const Domain & domain, const Problem & problem,std::string planFile){
    //
    // read plan
    //

    std::ifstream fIn(planFile);

	std::vector<std::string> plan;
    std::string line;

    // read plan from file
    while (std::getline(fIn, line)) {
        int i = line.find(")(");
        while (i != std::string::npos) { // split lines with multiple actions in it
			std::string action = line.substr(0, i + 1);
            line = line.substr(i + 1, line.length());
            plan.push_back(action);
            i = line.find(")(");
        }
        plan.push_back(line);
    }


	given_plan_typing_information typingInfo;


	std::unordered_map<std::string, int> taskNameMapping;
    for (int i = 0; i < domain.nPrimitiveTasks; i++) {
        taskNameMapping[domain.tasks[i].name] = i;
        if (domain.tasks[i].name.rfind("__") == 0) { // technical actions start with two underscores
            typingInfo.artificialTasks.insert(i);
        }
    }

	
	std::unordered_map<std::string, int> objectNameMapping;
    for (unsigned int i = 0; i < domain.constants.size(); i++)
        objectNameMapping[domain.constants[i]] = i;



    // generate set of distinct actions and sequence of plan steps
    bool usinglowercase = false;
	for (int i = 0; i < plan.size(); i++) {
        line = plan[i];
        if (usinglowercase) {
            transform(line.begin(), line.end(), line.begin(), [](unsigned char c){ if (c == '-') return int('_'); return tolower(c); });
        }
        if (line.rfind(';') == 0) continue; // skip comments
        line = line.substr(1, line.length() - 2);

		int indexOfOpeningBrace = line.find("[");

		std::string taskName = line.substr(0,indexOfOpeningBrace);
		std::string argumentString = line.substr(indexOfOpeningBrace+1,line.size()-indexOfOpeningBrace - 2);
		
		
		DEBUG(std::cout << i << " " << taskName << " " << argumentString << std::endl);

		// extract the arguments as strings
		std::stringstream argumentSS(argumentString);
		std::vector<std::string> arguments;
		std::string _temp;
		while(std::getline(argumentSS, _temp, ','))
			arguments.push_back(_temp);


		int taskNumber = -1;


        auto iter = taskNameMapping.find(taskName);
        if (iter == taskNameMapping.end()) {
            // try with lower case
			std::cerr << "- Did not find action \"" << taskName << "\", trying lower case." << std::endl;

			// in that case re-build the whole map
			taskNameMapping.clear();
		    for (int i = 0; i < domain.nPrimitiveTasks; i++) {
				std::string name = domain.tasks[i].name;
                transform(name.begin(), name.end(), name.begin(), [](unsigned char c){ if (c == '-') return int('_'); return tolower(c); });
		        
				taskNameMapping[name] = i;
		    }

            transform(taskName.begin(), taskName.end(), taskName.begin(), [](unsigned char c){ if (c == '-') return int('_'); return tolower(c); });


            iter = taskNameMapping.find(taskName);
            if (iter != taskNameMapping.end()) {
				std::cerr << "WARNING: Did not find mixed-case name of action, using lower case." << std::endl;
                taskNumber = iter->second;
                usinglowercase = true;
                continue;
            }
			std::cerr << "ERROR: task name not found: " << taskName << std::endl;
            exit(-1);
        } else {
            taskNumber = iter->second;
        }

		DEBUG(std::cout << "Task ID " << taskNumber << std::endl);

		std::vector<int> argumentIDs;
		for (unsigned int argIndex = 0; argIndex < arguments.size(); argIndex++){
			int argumentID = -1;
			
			std::string argumentName = arguments[argIndex];	


	        auto iter = objectNameMapping.find(argumentName);
	        if (iter == objectNameMapping.end()) {
	            // try with lower case
				std::cerr << "- Did not find object \"" << argumentName << "\", trying lower case." << std::endl;
	
				// in that case re-build the whole map
    			objectNameMapping.clear();
				for (unsigned int i = 0; i < domain.constants.size(); i++){
					std::string name = domain.constants[i];
	                transform(name.begin(), name.end(), name.begin(), [](unsigned char c){ if (c == '-') return int('_'); return tolower(c); });
			        objectNameMapping[name] = i;
				}

	            transform(argumentName.begin(), argumentName.end(), argumentName.begin(), [](unsigned char c){ if (c == '-') return int('_'); return tolower(c); });


	            iter = objectNameMapping.find(argumentName);
	            if (iter != objectNameMapping.end()) {
					std::cerr << "WARNING: Did not find mixed-case name of object, using lower case." << std::endl;
	                argumentID = iter->second;
	                usinglowercase = true;
	                continue;
	            }
				std::cerr << "ERROR: object name not found: " << argumentName << std::endl;
	            exit(-1);
	        } else {
	            argumentID = iter->second;
	        }
		
			argumentIDs.push_back(argumentID);
		}

		DEBUG(for (int x : argumentIDs)
			std::cout << " " << x;
		std::cout << std::endl);

		typingInfo.info[taskNumber].insert(argumentIDs);
    }
    
	
	fIn.close();

	return typingInfo; 
}

