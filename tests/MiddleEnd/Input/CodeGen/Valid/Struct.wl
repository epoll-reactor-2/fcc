// 9
// \todo: Now we get field with concrete index (for example, 1).
//        Make proper fields access with respect to StructGEP indices.
struct x {
    int a;
    int b;
    int c;
}

int main() {
    x a;
    a.a = 1;
    a.b = 2;
    a.c = 3;
    return a.a + a.b + a.c;
}