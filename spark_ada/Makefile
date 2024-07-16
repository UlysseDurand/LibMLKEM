proverewrites: proverewrite1 proverewrite2 proverewrite3 proverewrite4

proverewrite1:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:246 -f

proverewrite2:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:262 -f

proverewrite3:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:289 -f

proverewrite4:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:332 -f

proverewrite5:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:315 -f
	
proverewrite6:
	gnatprove -Pmlkem --limit-subp=recursntt.adb:343 -f

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

