#define Nclients	3

bool client_busy[Nclients]
bool Interrupt_set

inline disk_io()
{
    disk_busy = curproc
    assert(Interrupt_set == false)
    Interrupt_set = true
}

inline Serve_client(x)
{
    client_busy[x] = true
    curproc = x+1
    if    /* disk status */
    :: !disk_busy -> disk_io()
    :: else /* busy */ -> req_q!curproc
    fi
}

inline Handle()
{
    Interrupt_set = false
    client_busy[disk_busy-1] = false
    if
    :: req_q?curproc -> disk_io()
    :: empty(req_q)  -> disk_busy = 0
    fi
}

active proctype disk_sched()
{   chan req_q = [Nclients] of { byte }
    byte disk_busy, curproc

    do
    :: !client_busy[0] -> progress_0: Serve_client(0)
    :: !client_busy[1] -> progress_1: Serve_client(1)
    :: !client_busy[2] -> progress_2: Serve_client(2)
    :: Interrupt_set -> Handle()
    od
}

ltl p { [] (client_busy[1] -> <> !client_busy[1]) }

// exercise:
// 1.	negate the property, and check the error sequence found
// 2.	would it in principle be possible for both property p and
//	negated property !p to produce a counter-example?
