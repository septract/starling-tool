# Parses the output of 'count' repetitions of `./starling.sh --times BLAH.cvf`.
# Use with `awk -f parseTimes.cvf -v count=X`.

BEGIN {
	if (count < 1) count = 1;

	frontendPhases["Parse"] = 0;
	frontendPhases["Collate"] = 0;
	frontendPhases["Model"] = 0;

	proofgenPhases["Guard"] = 0;
	proofgenPhases["Graph"] = 0;
	proofgenPhases["Axiomatise"] = 0;
	proofgenPhases["GoalAdd"] = 0;
	proofgenPhases["Semantics"] = 0;
	proofgenPhases["TermGen"] = 0;
	proofgenPhases["Reify"] = 0;
	proofgenPhases["IterLower"] = 0;
	proofgenPhases["Flatten"] = 0;
	proofgenPhases["SymProof"] = 0;

	optimisePhases["GraphOptimise"] = 0;
	optimisePhases["TermOptimise"] = 0;

	backendPhases["Eliminate"] = 0;
	backendPhases["Backend"] = 0;

	for (phase in frontendPhases) times[phase] = 0;
	for (phase in proofgenPhases) times[phase] = 0;
	for (phase in optimisePhases) times[phase] = 0;
	for (phase in backendPhases) times[phase] = 0;

	terms["Success"] = 0;
	terms["NotSMT"] = 0;
}

# This should hopefully not capture method names
/^Phase [A-Z][A-Za-z]+;/ {
	# Name is always trailed by a semicolon
	name = substr($2, 0, length($2) - 1);
	# Time is always trailed by a semicolon
	time = substr($4, 0, length($4) - 2);

	times[name] += time;
	print "Phase:" name, time;
}

# Assuming all terms are successful or not SMT solvable!
/^[_0-9a-zA-Z]+: success$/ {
	terms["Success"]++;
}
/^[_0-9a-zA-Z]+: not SMT solvable$/ {
	terms["NotSMT"]++;
}

END {
	frontend = 0
	for (phase in frontendPhases) frontend += times[phase];
	proofgen = 0
	for (phase in proofgenPhases) proofgen += times[phase];
	optimise = 0
	for (phase in optimisePhases) optimise += times[phase];
	backend = 0
	for (phase in backendPhases) backend += times[phase];

	total = frontend + proofgen + optimise + backend;

	print "Total:Frontend", frontend / count;
	print "Total:Proofgen", proofgen / count;
	print "Total:Optimise", optimise / count;
	print "Total:Backend", backend / count;
	print "Total:*", total / count;

	tterms = 0;
	for (termtype in terms) {
		print "NTerms:" termtype, terms[termtype] / count;
		tterms += terms[termtype];
	}
	print "NTerms:*", tterms / count;
}
