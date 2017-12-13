all: HOASProofs.vo Equations.vo

Monad.vo: Monad.v
	coqc Monad.v

Prelim.vo: Prelim.v
	coqc Prelim.v

Complex.vo: Complex.v Prelim.vo
	coqc Complex.v

Matrix.vo: Matrix.v Complex.vo 
	coqc Matrix.v 

Quantum.vo: Quantum.v Matrix.vo
	coqc Quantum.v

Contexts.vo: Contexts.v Prelim.vo
	coqc Contexts.v 

HOASCircuits.vo: HOASCircuits.v Contexts.vo
	coqc HOASCircuits.v

TypeChecking.vo: TypeChecking.v HOASCircuits.vo
	coqc TypeChecking.v

HOASExamples.vo: HOASExamples.v TypeChecking.vo
	coqc HOASExamples.v

DBCircuits.vo : DBCircuits.v HOASCircuits.vo Monad.vo
	coqc DBCircuits.v

FlatCircuits.vo: FlatCircuits.v HOASCircuits.vo Monad.vo
	coqc FlatCircuits.v

Denotation.vo: Denotation.v Quantum.vo DBCircuits.vo
	coqc Denotation.v

HOASProofs.vo: HOASProofs.v HOASExamples.vo Denotation.vo
	coqc HOASProofs.v

Equations.vo: Equations.v TypeChecking.vo Denotation.vo
	coqc Equations.v


#MachineProofs.vo: MachineProofs.v MachineExamples.vo Denotation.vo
#	coqc MachineProofs.v

#MachineCircuits.vo : MachineCircuits.v Contexts.vo FlatCircuits.vo HOASCircuits.vo Denotation.vo
#	coqc MachineCircuits.v

#MachineExamples.vo: MachineExamples.v MachineCircuits.vo
#	coqc MachineExamples

#FlatProofs.vo: FlatProofs.v FlatExamples.vo Denotation.vo
#	coqc FlatProofs.v


clean:
	rm *.vo
