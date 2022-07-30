int f(int arg1, int arg2) {
    --arg1;
    --arg2;
    return arg1 + arg2;
}

int main() {
    int arg1 = 100;
    int arg2 = 200;
    return f(arg1, arg2);
}