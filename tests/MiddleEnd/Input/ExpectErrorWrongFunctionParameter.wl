// ERROR at line 9, column 15: Type mismatch: i8* got, but i32 expected
int f(int arg) {
    return arg;
}

int main() {
    string arg = "OK";
    return f(arg);
}