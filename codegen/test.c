#include <stdio.h>


struct stack {
    struct stack* prev;
    int* val;
} *sp;



void push(struct stack* item, int* val) {
    item->prev = sp;
    item->val = val;
    printf("*************** %d\n", *val);
    sp = item;
}

int* pop() {
    int* val = sp->val;
    sp = sp->prev;
    return val;
}

int main() {
    struct stack item1;
    int x1 = 100;
    push(&item1, &x1);

    struct stack item2;
    int x2 = 200;
    push(&item2, &x2);

    pop();

    printf("%d\n", *sp->val);

    return 0;
}
