//1
float __fabs(float x) {
    if (x < 0.0) {
        return x * -1.0;
    } else {
        return x;
    }
    return -999999.999999;
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

float mod(float x) {
    if (x < 0.00) {
        return x * -1.00;
    } else {
        return x;
    }
    return 0.00;
}

int main() {
    return mod(__sqrt(81.00) - 9.00000000001) < 0.00001;
}