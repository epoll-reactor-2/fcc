//1
float __fabs(float x) {
    if (x < 0.0) {
        return x * -1.0;
    } else {
        return x;
    }
    return -9999999999.9999;
}

float __sqrt(float x) {
    if (x < 0.0) {
        return -1.0;
    }

    float guess = x;
    float epsilon = 0.0001;

    while (__fabs(guess * guess - x) > epsilon) {
        guess = 0.5 * (guess + x / guess);
    }

    return guess;
}

int main() {
    return __sqrt(81.00) == 9.00;
}