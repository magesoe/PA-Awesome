This program was developed for the course 02242 Program Analysis on Denmark Technical University.

The program does 4 analysis at once.

* Reaching Definition
* Live Variables
* Detection of Signs
* Interval

It expects 4 parameters.

* Path to a file with a program in the MicroC language
* A boolean indicating whether or not to use queues in the worklist algorithm. Uses a stack otherwise.
* An integer representing the minimum value used in the Interval analysis
* An integer representing the maximum value used in the Interval analysis

The structure of the program is.
* Domain.fs: Contains the type definitions used in the program.
* Parser.fs/Parser.fsy: Contains the definition for the parser.
* Lexer.fs/Lexer.fsl: Contains the definition for the lexer.
* ProgramGraph.fs: Contains the functions that turn the AST into a program graph.
* WorklistAlgo.fs: Contains the definition of the worklist algorithm.
* Analysis/*.fs: This folder contains the definition of each analysis.
* AnalysisStructures.fs: Contains common structures used when applying the analysis.
* Analysis.fs: Contains a function for each analysis, which applies the given analysis.
* Program.fs/AssemblyInfo.fs: Contains the console application part of the program.