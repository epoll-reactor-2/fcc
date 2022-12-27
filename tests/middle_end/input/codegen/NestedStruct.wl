// 123
struct a {
    struct b {
        struct c {
            int d;
        };
        c cc;
        int e;
    };
    b bb;
}

int main() {
    a aa;
    aa.bb.cc.d = 123;
    aa.bb.e = 1;
    return aa.bb.cc.d + aa.bb.e;
}
