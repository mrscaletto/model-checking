module stack

open util/ordering[State] as ord

enum Action {
    POP,
    PUSH,
    STUTTER
}

one sig DataManager {
    freeElems: set Node
}

one sig Stack {
    root: lone Node
}

sig Node {
    nxt: lone Node
}

sig Event {
    pre, post: one Stack
}

sig Push extends Event {
    value: Node
} {
    post.root = value
    value.nxt = pre.root
}

sig Pop extends Event {
    popped: one Node
} {
    popped = pre.root
    post.root = pre.root.nxt
}

sig State {
    s: one Stack,
    act: Action,
    deleted: set Node
}

fun first_elem: lone Node { Stack.root }

fun reachable[n: Node]: set Node {
    n.*nxt - n
}

fact noDeleted {
    no n: Node | n in State.deleted and n in State.s.root.*nxt
}

fact nxtNotSelf {
    no n: Node | n = n.nxt
}

fact allNodesBelong {
    all n: Node | one s: Stack | n in s.root.*nxt
}

fact nxtNotCyclic {
    no n: Node | n in reachable[n]
}

pred stutter() {
    State'.act = STUTTER
    State'.s = State.s
    State'.deleted = State.deleted
}

pred push[new: Node] {
    new not in State.s.root.*nxt -- avoid already existing node as new push value

    State'.act = PUSH
    State'.s.root = new
    new.nxt' = State.s.root

    DataManager.freeElems' = DataManager.freeElems - new
    State'.deleted = State.deleted
}

pred pop {
    State.s.root != none -- ensure stack is not empty when popping

    State'.act = POP
    State'.s.root = State.s.root.nxt
    State'.deleted = State.deleted + State.s.root

    DataManager.freeElems' = DataManager.freeElems + State.s.root
}

pred transition {
    stutter or (some n: Node | push[n]) or pop
}

pred StackIsValid {
    -- root (head) is not null
    one Stack.root

    -- elements that are in the stack cannot be in freeElems
    all n: Stack.root.*nxt | n not in DataManager.freeElems

    -- union of sets is complete: each element is either in the stack or in freeElems
    all e: Node | e in Stack.root.*nxt or e in DataManager.freeElems

    -- free elements should not have any nxt nodes
    all e: DataManager.freeElems | no e.nxt

    -- ensuring acyclic nature of stack
    no n: Stack.root.*nxt | n in reachable[n]

    -- Check linearity: no two elements have the same nxt element
    all disj n1, n2: Stack.root.*nxt | n1.nxt != n2.nxt

    -- no element points back to root
    all n: Stack.root.*nxt | Stack.root != n.nxt

    -- Check connections: each node has at most one nxt
    all n: Stack.root.*nxt | lone n.nxt

    -- Check connections: each nxt node should not be a free element
    all n: Stack.root.*nxt | lone n.nxt and n.nxt not in DataManager.freeElems
}

fact "init" {
    -- Initial conditions
    some Stack.root -- make sure the stack is not initially empty
    #Node > 6
    #Stack.root.*nxt > 3
    StackIsValid
}

run {
    always transition
} for 12 but 1..10 steps

-- Утверждение popThenPush: если сделать pop после push, стек должен вернуться в исходное состояние
assert popThenPush {
    all s: Stack, val: Node |
        some e: Push, p: Pop |
        e.pre = s and e.value = val and
        p.pre = e.post and p.popped = val and
        p.post = s =>
        p.post.root = s.root
}

-- Проверка popThenPush
check popThenPush for 5 Push, 5 Pop, exactly 10 Node

-- Утверждение sameNumberPushesPops: количество операций push и pop должно быть одинаковым
assert sameNumberPushesPops {
    all s: Stack |
        let pushes = {e: Push | e.pre = s},
            pops = {e: Pop | e.pre = s} |
        #pushes = #pops
}

-- Проверка sameNumberPushesPops
check sameNumberPushesPops for 5 Push, 5 Pop, exactly 10 Node

-- Утверждение noPopFromEmpty: нельзя выполнить pop из пустого стека
assert noPopFromEmpty {
    all s: Stack | no s.root => no {e: Pop | e.pre = s}
}

-- Проверка noPopFromEmpty
check noPopFromEmpty for 5 Push, 5 Pop, exactly 10 Node

