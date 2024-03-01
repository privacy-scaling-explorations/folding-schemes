pragma circom 2.0.3;

template Example () {
    signal input ivc_input[1];
    signal output ivc_output[1];   
    signal temp;
    
    temp <== ivc_input[0] * ivc_input[0];
    ivc_output[0] <== temp * ivc_input[0] + ivc_input[0] + 5;
    ivc_output[0] === 35;
}

component main { public [ivc_input] } = Example();