// 1
int f(int arg1, int arg2) {
    --arg1;
    --arg2;
    return arg1 + arg2;
}

int main() {
    int res = f(100, 200);
    return res == 298;
}