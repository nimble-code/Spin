never {
	skip;	/* match first step of init (spin version 2.0) */
	do
	:: !pres_to_ses[0]?[transfer]
	&& !flow_to_ses[0]?[connect]
	:: pres_to_ses[0]?[transfer] ->
		goto accept0
	:: flow_to_ses[0]?[connect] ->
		goto accept1
	od;
accept0:
	do
	:: !ses_to_pres[0]?[accept]
	&& !ses_to_pres[0]?[reject]
	od;
accept1:
	do
	:: !ses_to_pres[1]?[accept]
	&& !ses_to_pres[1]?[reject]
	od
}
