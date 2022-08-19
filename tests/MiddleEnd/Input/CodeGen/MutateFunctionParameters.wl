int f(int arg1, int arg2) {
    --arg1;
    --arg2;
    return arg1 + arg2;
}

int main() {
    int v1 = 100;
    int v2 = 200;
    return f(v1, v2);
}