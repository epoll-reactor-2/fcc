// Error at line 5, column 30: Cannot apply `+` to <INT> and <BOOLEAN>
int main() {
    int  i =   0;
    bool b = true;
    /* ??? */ int result = i + b;
    return 0;
}