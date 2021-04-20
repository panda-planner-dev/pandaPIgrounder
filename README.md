# pandaPIgrounder
This is the grounder of pandaPI



## Building
To compile pandaPIgrounder, you need to perform the following steps:

 - git clone https://github.com/panda-planner-dev/pandaPIgrounder.git
 - git submodule init
 - git submodule update
 - cd cpdl
 - make boruvka opts bliss
	- if you have lpsolve installed, you may also need to ```make lpsolve```
 - make
 - cd ../src
 - make

## Command Line Options
The general syntax for a pandaPIgrounder call is
```
./pandaPIgrounder INPUT OUTPUT
```

Run `./pandaPIgrounder -h` to get a more detailed description of the command line options of pandaPIgrounder.
