Title:
Gradual Verification with Dafny

Abstract:
High assurance systems are challenging to implement because failure risks harm to stake holders.
The traditional design approach builds assurance in such systems through requirements, tests, and code reviews.
The process, though rigorous, does not provide formal guarantees on system behavior.
Another approach builds assurance by modeling the system and proving properties on the model.
The properties transfer to the real world if the model represents the desired system and is a sound abstraction of the actual implementation.
The work in this presentation brings the two paradigms together through gradual verification.
Gradual verification writes tests to build assurance in both the implementation and model.
A test in this context therefore must pass the implementation and must prove out in the modeling framework.
The work in this presentation further introduces a testing framework for the Dafny modeling environment and illustrates gradual verification with a simple example.
It claims that gradual verification is more approachable to non-experts in modeling and yields a stronger assurance case than either paradigm on its merits.

Bio:
Eric Mercer is an Associate Professor at Brigham University in the Department of Computer Science. 
He received his Ph.D. in Electrical Engineering from the University of Utah in 2002.
His research interests are in automatic test generation, program analysis, formal verification, and model based systems engineering.
