// Error at line 5, column 30: Cannot apply `+` to <STRING> and <BOOLEAN>
int main() {
    string s =   "";
    bool   b = true;
    /* ??? */ int result = s + b;
    return 0;
}