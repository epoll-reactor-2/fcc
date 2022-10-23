// 1
int puts(string data);
int strcmp(string str1, string str2);

int main() {
    string mem = "?:!<";
    mem[0] = '>';
    // puts(mem);
    return strcmp(mem, ">:!<") == 0;
}