// Error at line 8, column 14: Type mismatch: i8* and i32
int f(int arg) {
    return arg;
}

int main() {
    string arg = "OK";
    return f(arg);
}
