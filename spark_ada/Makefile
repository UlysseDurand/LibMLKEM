proverewrite1:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:218

proverewrite2:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:235

proverewrite3:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:256

proverewrite3bis:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:273

proverewrite4:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:299

proverecurs:
	gnatprove -Pmlkem -u src/recursntt.adb --info

proverecursmain:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:11 --counterexamples=off


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

