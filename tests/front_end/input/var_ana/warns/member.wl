//W<7:5>: Variable `t1` is never used
struct type {
    int x;
}

int main() {
    type t1;
    type t2;
    t2.x = 1;
    return t2.x;
}
