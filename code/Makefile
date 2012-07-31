Main: Main.agda Accel.o Generator.o
	agda -i. -i/Users/thiemann/darcs/agda-lib/src -c Main.agda

Main2: Main2.agda Accel.o
	agda -i. -i/Users/thiemann/darcs/agda-lib/src -c Main2.agda

Accel.o: Accel.hs
	ghc -c Accel.hs

Generator.o: Generator.hs Accel.o
	ghc -c Generator.hs
