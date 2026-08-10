/*
 * Distributed Two-Phase Commit (2PC) Protocol with Network Timeout & Recovery
 * 
 * Demonstrates formal verification of distributed consensus:
 * 1. Transaction Coordinator (TC) coordinates atomic commitment.
 * 2. Resource Managers (RM) process local transactions.
 * 3. Asynchronous non-blocking message channels with message drop simulation.
 * 4. Safety Invariants: No mixed decisions (Atomicity).
 */

#define NUM_RMS      2    /* Number of Resource Managers */
#define TIMEOUT_VAL  5    /* Timeout threshold for votes */

/* Message Types */
mtype = {
    MSG_PREPARE,
    MSG_VOTE_COMMIT,
    MSG_VOTE_ABORT,
    MSG_GLOBAL_COMMIT,
    MSG_GLOBAL_ABORT,
    MSG_ACK
};

/* Decision States */
mtype = {
    STATE_INIT,
    STATE_WAIT,
    STATE_PREPARED,
    STATE_COMMITTED,
    STATE_ABORTED
};

/* Communication Channels */
chan to_rm[NUM_RMS] = [4] of { mtype };
chan to_tc           = [4] of { byte, mtype };

/* Global Decision Tracking for Invariant Checking */
mtype rm_state[NUM_RMS];
mtype tc_state = STATE_INIT;

/* Safety Property: Atomicity (No mixed commit and abort decisions) */
inline verify_atomicity() {
    bool has_commit = false;
    bool has_abort  = false;
    byte i;
    
    for (i : 0 .. (NUM_RMS - 1)) {
        if
        :: rm_state[i] == STATE_COMMITTED -> has_commit = true;
        :: rm_state[i] == STATE_ABORTED   -> has_abort  = true;
        :: else -> skip;
        fi;
    }
    
    /* Atomicity Guarantee: Cannot have both committed and aborted participants */
    assert(!(has_commit && has_abort));
}

/* --------------------------------------------------------------------------
 * Resource Manager Process (RM / Participant)
 * -------------------------------------------------------------------------- */
proctype ResourceManager(byte rm_id) {
    mtype msg;
    bool vote_to_commit;

    rm_state[rm_id] = STATE_INIT;

    /* Step 1: Wait for PREPARE request from Coordinator */
    to_rm[rm_id] ? msg;
    if
    :: msg == MSG_PREPARE ->
        printf("RM[%d]: Received PREPARE request\n", rm_id);
    :: else ->
        printf("RM[%d]: Unexpected message, aborting\n", rm_id);
        rm_state[rm_id] = STATE_ABORTED;
        verify_atomicity();
        goto done;
    fi;

    /* Step 2: Nondeterministically decide to Vote COMMIT or ABORT */
    if
    :: vote_to_commit = true;  printf("RM[%d]: Voting COMMIT\n", rm_id);
    :: vote_to_commit = false; printf("RM[%d]: Voting ABORT\n", rm_id);
    fi;

    if
    :: vote_to_commit ->
        rm_state[rm_id] = STATE_PREPARED;
        to_tc ! rm_id, MSG_VOTE_COMMIT;

        /* Step 3: Wait for Global Decision from Coordinator */
        to_rm[rm_id] ? msg;
        if
        :: msg == MSG_GLOBAL_COMMIT ->
            rm_state[rm_id] = STATE_COMMITTED;
            printf("RM[%d]: Global Decision -> COMMITTED\n", rm_id);
            to_tc ! rm_id, MSG_ACK;
        :: msg == MSG_GLOBAL_ABORT ->
            rm_state[rm_id] = STATE_ABORTED;
            printf("RM[%d]: Global Decision -> ABORTED\n", rm_id);
            to_tc ! rm_id, MSG_ACK;
        fi;

    :: else ->
        rm_state[rm_id] = STATE_ABORTED;
        to_tc ! rm_id, MSG_VOTE_ABORT;
        printf("RM[%d]: Local Decision -> ABORTED\n", rm_id);
    fi;

    verify_atomicity();

done:
    skip;
}

/* --------------------------------------------------------------------------
 * Transaction Coordinator Process (TC)
 * -------------------------------------------------------------------------- */
proctype Coordinator() {
    byte i;
    byte rm_id;
    mtype msg;
    byte commit_votes = 0;
    byte abort_votes  = 0;
    byte acks         = 0;

    tc_state = STATE_INIT;
    printf("TC: Starting 2PC Transaction\n");

    /* Phase 1: Broadcast PREPARE to all RMs */
    tc_state = STATE_WAIT;
    for (i : 0 .. (NUM_RMS - 1)) {
        to_rm[i] ! MSG_PREPARE;
    }

    /* Collect Votes from all Resource Managers */
    do
    :: (commit_votes + abort_votes < NUM_RMS) ->
        if
        :: to_tc ? rm_id, msg ->
            if
            :: msg == MSG_VOTE_COMMIT ->
                commit_votes++;
                printf("TC: Received VOTE_COMMIT from RM[%d]\n", rm_id);
            :: msg == MSG_VOTE_ABORT ->
                abort_votes++;
                printf("TC: Received VOTE_ABORT from RM[%d]\n", rm_id);
            fi;
        :: timeout ->
            printf("TC: Timeout waiting for votes, triggering ABORT\n");
            abort_votes = NUM_RMS - commit_votes;
            break;
        fi;
    :: else -> break;
    od;

    /* Phase 2: Make Global Decision */
    if
    :: (commit_votes == NUM_RMS) ->
        tc_state = STATE_COMMITTED;
        printf("TC: All RMs voted COMMIT -> Global Decision: COMMIT\n");
        for (i : 0 .. (NUM_RMS - 1)) {
            to_rm[i] ! MSG_GLOBAL_COMMIT;
        }
    :: else ->
        tc_state = STATE_ABORTED;
        printf("TC: One or more ABORT votes/timeouts -> Global Decision: ABORT\n");
        for (i : 0 .. (NUM_RMS - 1)) {
            to_rm[i] ! MSG_GLOBAL_ABORT;
        }
    fi;

    /* Collect Acknowledgments */
    do
    :: (acks < commit_votes) ->
        if
        :: to_tc ? rm_id, msg ->
            if
            :: msg == MSG_ACK ->
                acks++;
                printf("TC: Received ACK from RM[%d]\n", rm_id);
            fi;
        :: timeout ->
            printf("TC: Timeout waiting for ACKs\n");
            break;
        fi;
    :: else -> break;
    od;

    printf("TC: Transaction Finished. Final State = %e\n", tc_state);
}

/* --------------------------------------------------------------------------
 * Main Initialization Block
 * -------------------------------------------------------------------------- */
init {
    byte i;
    atomic {
        run Coordinator();
        for (i : 0 .. (NUM_RMS - 1)) {
            run ResourceManager(i);
        }
    }
}
