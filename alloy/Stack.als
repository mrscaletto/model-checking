module stack

sig item {}

one sig Stack {
    var Top: lone item,    -- верхний элемент стека (может быть пустым)
    var elems: set item,   -- элементы в стеке
    var deleted: set item  -- элементы, удалённые из стека
}

fun v_top : lone item { Stack.Top }

-- Описание операции push
pred push[e: item] {
    -- Предусловие: элемент удалён
    e in Stack.deleted

    -- Действие
    Stack.deleted' = Stack.deleted - e
    Stack.elems' = Stack.elems + e
    Stack.Top' = e
}

-- Описание операции pop
pred pop {
    -- Предусловие: стек не пуст
    some v_top

    -- Действие
    Stack.deleted' = Stack.deleted + v_top
    Stack.elems' = Stack.elems - v_top

    -- Обновление верхнего элемента
    Stack.Top' = none
    some Stack.elems' => Stack.Top' =  Stack.elems'
}

-- Описание операции clear
pred clear {
    -- Действие
    Stack.deleted' = Stack.deleted + Stack.elems
    Stack.elems' = none
    Stack.Top' = none
}

-- Инварианты стека
pred StackIsValid {
    -- Элементы должны принадлежать какому-либо одному множеству
    all i: item | i in Stack.elems or i in Stack.deleted

    -- верхний элемент должен быть из elems или пуст
    no Stack.Top or Stack.Top in Stack.elems
}

fact "init" {
    #item > 4
    some Stack.elems 
    StackIsValid
}

-- Проверка изменения, если никаких действий не произошло
pred noChange { 
    Stack.elems' = Stack.elems and
    Stack.deleted' = Stack.deleted and
    Stack.Top' = Stack.Top
}

-- Возможные переходы
pred transitions { 
    (some e: item | push[e]) or 
    pop or 
    clear or
    noChange
}

run transitions for 5 but 1..2 steps

-- Проверки корректности
pred sc1 {
    -- Возможность удаления элемента
    eventually some Stack.deleted
}

run sc1 for 5 but 1..2 steps

pred sc2 {
    -- Возможность опустошения стека
    eventually no Stack.elems
}

run sc2 for 5 but 1..2 steps

pred sc3 {
    -- Операция push выполняется
    eventually some e: item {
        e in Stack.deleted
        e in Stack.elems'
    }
}

run sc3 for 5 but 1..2 steps

pred sc4 {
    -- Операция pop выполняется
    eventually some e: item {
        e in Stack.elems
        e in Stack.deleted'
    }
}

run sc4 for 5 but 1..2 steps

