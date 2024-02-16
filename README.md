## More Background Information

We've put together a website with the history of all planning systems of the PANDA family, links to all relevant software projects, and further background information including pointers explaining the techniques deployed by the respective systems.

You find it on https://panda-planner-dev.github.io/ or, as a forward, on http://panda.hierarchical-task.net

# pandaPIgrounder

This is the grounder of pandaPI


## Building

To be able to compile pandaPIgrounder you need zip (required by CPDDL) and gengetopt (tested with version 2.23).
To compile pandaPIgrounder, you need to perform the following steps:

```
git clone https://github.com/panda-planner-dev/pandaPIgrounder.git
cd pandaPIgrounder
git submodule init
git submodule update
cd cpddl
git apply ../0002-makefile.patch
make boruvka opts bliss lpsolve
make
cd ../src
make
```

To run all these commands, you can execute the `build.sh` script.

## Command Line Options

The general syntax for a pandaPIgrounder call is
```
./pandaPIgrounder INPUT OUTPUT
```

Run `./pandaPIgrounder -h` to get a more detailed description of the command line options of pandaPIgrounder.

## Capabilities

The pandaPIgrounder can ground most instances used in the [International Planning Competition (IPC) 2023](https://ipc2023-htn.github.io/).
However some instances in the IPC were too large to be grounded.
For those, we recommend to use one of the lifted HTN planners (e.g. [lilotane](https://github.com/domschrei/lilotane) or [HyperTensioN](https://github.com/Maumagnaguagno/HyperTensioN)).

If you use the IPC constraints (8 GB of RAM and 30 minutes of runtime), there are 57 instances that can't be grounded.
In all cases, the problem is insufficient RAM.

You can find [a list](https://github.com/panda-planner-dev/pandaPIgrounder/blob/master/doc/ungroundable-ipc-problems.txt) of all instances that will fail grounding in this repo.
This list contains the file names of the problem files that are not groundable in the IPC setting.
The given lists refers to the instances in the [IPC 2023 domain repo](https://github.com/ipc2023-htn/ipc2023-domains).
