// 123
struct x {
    int *ptr;
}

void change(x *ptr) {
    *(*ptr).ptr = 123;
}

int main() {
    x object;
    int mem = 0;
    object.ptr = &mem;
    change(&object);
    return *object.ptr;
}
