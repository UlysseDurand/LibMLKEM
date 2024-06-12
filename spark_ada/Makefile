proveref:
	gnatprove -Pmlkem -u src/refmlkem.adb --info

provesum:
	gnatprove -Pmlkem -u src/sumgen.adb

prove:		
	gnatprove -Pmlkem -u src/sumgen.adb
	gnatprove -Pmlkem -u src/mylemmas.adb
	gnatprove -Pmlkem -u src/mlkem.adb
	gnatprove -Pmlkem -u src/refmlkem.adb

compile:
	gprbuild -Pmlkem

