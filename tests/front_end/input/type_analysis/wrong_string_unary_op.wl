// Error at line 8, column 5: Cannot apply `--` to string
int main() {
    int num = 0;
    --num;
    char sym = 'a';
    --sym;
    string val = "Hello";
    --val;
    return 0;
}