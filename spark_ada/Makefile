proverewrite1:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:185 -f

proverewrite2:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:201 -f

proverewrite3:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:228 -f

proverewrite4:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:271 -f

proverecurs:
	gnatprove -Pmlkem -u src/recursntt.adb --info

proverecursmain:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:11 --counterexamples=off --info

proverecursequiv:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:47 --counterexamples=off --info


proveref:
	gnatprove -Pmlkem -u src/refmlkem.adb --info

provesum:
	gnatprove -Pmlkem -u src/sumgen.adb

prove:		
	gnatprove -Pmlkem -u src/sumgen.adb
	gnatprove -Pmlkem -u src/mylemmas.adb
	gnatprove -Pmlkem -u src/mlkem.adb
	gnatprove -Pmlkem -u src/refmlkem.adb
	gnatprove -Pmlkem -u src/recursntt.adb

compile:
	gprbuild -Pmlkem

