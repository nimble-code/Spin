/* Alg. 5.9 Apt & Olderog book,
 * 'Manna-Pnueli central server algorithm
 */

byte cnt, request, respond

active proctype server()
{
	do
	:: (request != 0) ->
		respond = request
		(respond == 0)
		request = 0
	od
}

active [2] proctype client()
{
	assert(_pid > 0)
	do
	:: respond != _pid
		request = _pid
	:: else ->
		cnt++
		assert(cnt == 1) /* critical section */
		cnt--
		respond = 0
	od
}
