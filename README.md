# pandaPIgrounder
This is the grounder of pandaPI



## Building
To compile pandaPIgrounder, you need to perform the following steps:

 - check out
 - git submodule init
 - git submodule update
 - cd cpdl
 - make boruvka opts bliss
	- if you have lpsolve installed, you may also need to ```make lpsolve```
 - make
 - cd ../src
 - make

## Command line options
The general syntax for a pandaPIgrounder call is
```
./pandaPIgrounder INPUT OUTPUT
```

You may want to add one of the following command line options

 - -q: Quiet mode, no output will be produced except for the output file
 - -i: Invariant synthesis, will lead to output containing SAS+ variables
 - -2: Compute H2 mutexes, will compute H2 mutexes and output them
 - -a: For SAS+ variables, add all deletes to actions, not just the necessary ones
 - -n: For SAS+ variables, output no deletes effects
 - -S: Force SAS+ output for every variable
 - -N: Compile binary SAS+variables if possible, may lead to more action in the output but reduces the number of facts
 - -g: Only ground, don't write the grounded instance
 - -l: No literal pruning, do not remove irrelevant facts
 - -e: No abstract expansion, do not expand abstract tasks with only one applicable method
 - -m: No method precondition pruning, do not remove method precondition actions, that carry neither preconditions nor effects (due to literal pruning)
 - -h: Disable hiearchy typing. This will not change the grounding, but will only make the grounding slower on some domains (especially Minecraft)
 - -f: Enable future precondition caching. This will not change the grounding, but is a technique to try to make the GPG faster
 - -D: Remove duplicat actions. This does only apply to artificial primitive tasks (the ones inserted for method preconditions or other compilations) currently
 - -E: No empty methods. Adds a zero-cost no-op to empty methods. The pandaPIengine's progression planner needs this property

Don't use the command line option ``-in``, as gengetopt will missinterpret it.
