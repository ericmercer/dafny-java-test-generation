# dafny-java-test-generation
[Get Daphny from Source](https://github.com/dafny-lang/dafny/wiki/INSTALL#building-and-developing-from-source-code)
* Install .Net 5.0
*	Install python 3
    * sudo apt install python3 python3-pip
*	Install Java and Gradle
*	Make a Base Directory
    *	mkdir BASE-DIRECTORY
*	Download Daphny Source
    *	cd BASE-DIRECTORY
    *	git clone https://github.com/dafny-lang/dafny.git --recurse-submodules
    *	cd dafny
    *	make exe
    *	pip3 install pre-commit
    *	pre-commit install
    *	make runtime
*	Install Z3 version 4.8.5
    *	cd BASE-DIRECTORY
    *	wget https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip
    *	unzip z3-4.8.5-x64-ubuntu-16.04.zip
    *	mv z3-4.8.5-x64-ubuntu-16.04 dafny/Binaries/z3
*	Set up Java:
    *	make -C ${DAFNY} runtime
*	For testing
    *	pip3 install lit OutputCheck
        *	Might need to add to path.
    * Run tests:
        *	cd BASE_DIRECTORY/dafny/Test; lit .
*	Run Daphny:
    *	BASE_DIRECTORY/dafny/Scripts/dafny <MY-PROGRAM.dfy>
[Generating Tests](https://github.com/Dargones/dafny/tree/PatchesToCounterExamples/Source/DafnyTestGeneration#how-to-generate-tests)
*	Always use command line argument:
    *	/definiteAssignment:3
*	Test Mode
    *	/generateTestMode:<TYPE>
        *	Block
        *	Path
*	Dead Code
    *	/warnDeadCode
*	Loops
    *	/loopUnroll
    *	/generateTestSeqLengthLimit
*	Test using example at above link
