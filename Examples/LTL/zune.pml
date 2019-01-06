/*
 * input: days elapsed since Jan 1, 1980
 * intended output: year and daynr in current year
 *
 * a bug caused all Zune-30 players to freeze on Dec 31, 2008
 * http://www.zuneboards.com/forums/zune-news/38143-cause-zune-30-leapyear-problem-isolated.html
 *
 * Wikepedia:
 * The bug was in the firmware clock-driver, which was written by Freescale
 * for their MC13783 PMIC processor. The same bug froze up Toshiba Gigabeat S
 * media players that share the same hardware and driver.
 */

#define IsLeapYear(y)	(((y%4 == 0) && (y%100 != 0)) || (y%400 == 0))

chan q = [0] of { short };

active proctype zune()
{	short year = 1980;
	short days;

end:	do
	:: q?days ->
S:		do
		:: days > 365 ->
			if
			:: IsLeapYear(year) ->
				if
				:: days > 366 ->
					days = days - 366;
					year++
				:: else
#ifdef FIX
					-> break
#endif
				fi
			:: else ->
				days = days - 365;
				year++
			fi
		:: else ->
			break
		od;
E:		printf("Year: %d, Day %d\n", year, days)
	od;
	/* check that the date is in a valid range */
	assert(days >= 1 && days <= 366);
	assert(days < 366 || IsLeapYear(year))
}

init {
	/* jan 1, 2008 */
	short days = (2008 - 1980) * 365 + (2008-1980)/4;

	if
	:: q!days + 365
	:: q!days + 366
	:: q!days + 367
	fi
}

ltl p1 { [] (( zune@S ) -> ( <> zune@E ) ) }

/* sample analysis:
	spin -a zune.pml	# spin version 6 or later
	cc -o pan pan.c		# compile
	./pan -a -N p1		# find matches of formula
	spin -t -p -l zune.pml	# replay error sequence
 */

