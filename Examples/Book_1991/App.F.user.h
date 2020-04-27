/*
 * User Layer Validation Model
 */

proctype userprc(bit n)
{
	use_to_pres[n]!transfer;
	if
	:: pres_to_use[n]?accept -> goto Done
	:: pres_to_use[n]?reject -> goto Done
	:: use_to_pres[n]!abort  -> goto Aborted
	fi;
Aborted:
	if
	:: pres_to_use[n]?accept -> goto Done
	:: pres_to_use[n]?reject -> goto Done
	fi;
Done:
	skip
}
