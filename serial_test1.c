/*
 * serial_gets.c
 *
 *  Created on: Dec 4, 2019  3:30 am
 *      Author: rajsa
 *  All steps of project except ARB command
 */
// Serial Example
// Jason Losh
//-----------------------------------------------------------------------------
// Hardware Target
//-----------------------------------------------------------------------------
// Target Platform: EK-TM4C123GXL Evaluation Board
// Target uC:       TM4C123GH6PM
// System Clock:    40 MHz
// Hardware configuration:
// Red LED:
//   PF1 drives an NPN transistor that powers the red LED
// Green LED:
//   PF3 drives an NPN transistor that powers the green LED
// UART Interface:
//   U0TX (PA1) and U0RX (PA0) are connected to the 2nd controller
//   The USB on the 2nd controller enumerates to an ICDI interface and a virtual COM port
//   Configured to 115,200 baud, 8N1
//-----------------------------------------------------------------------------
// Device includes, defines, and assembler directives
//-----------------------------------------------------------------------------
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>
#include<math.h>
#include <stdlib.h>
#include "tm4c123gh6pm.h"

// Pin bitbands
#define CS_NOT       (*((volatile uint32_t *)(0x42000000 + (0x400053FC-0x40000000)*32 + 5*4))) //Pb5 ~CS SSI2FSS
#define LDAC_NOT           (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 1*4))) //PF1 ~LDAC

// PortD masks
#define CS_NOT_MASK 32
#define LDAC_NOT_MASK 2
#define AIN0_MASK 8

//AIN masks
#define AIN1_MASK 4
#define GREEN_LED    (*((volatile uint32_t *)(0x42000000 + (0x400253FC-0x40000000)*32 + 3*4)))

#define GREEN_LED_MASK 8
#define RED_LED_MASK 2
#define pi 3.14159265

#define delay4Cycles() __asm(" NOP\n NOP\n NOP\n NOP")
#define max_Arg 6
#define  Max_letter  80  // Maximum size of input command buffer.
char input[Max_letter]; // Input buffer

uint8_t position[6];
uint8_t arg_count;
char param_array[max_Arg][20] = { 0 };
char temp_param[20] = "";
uint8_t args_str = 0;
uint8_t args_no = 0;
uint32_t deltaphi, phi, deltaphi1, phi1 = 0;
bool chan1, chan2;
uint8_t channel;
float dcValue;
float freq;
float offset;
float dutyCycle;
float iVolt;
char str[80];

uint16_t DC[2] = { 0, 0 };
bool channel0[3] = { false, true, false };
bool channel1[3] = { false, true, false };
uint32_t ch0Cycle, ch1Cycle = 0;
float ch0Freq, ch1Freq = 0;
bool hibdiff = false;
uint16_t errorRaw[2] = { 0, 0 };
int16_t channel_0_slope = -384;
int16_t channel_1_slope = -387;
int16_t channel_0_intercept = 2036;
int16_t channel_1_intercept = 2056;
uint16_t channel_1_header = 45056;
int16_t channel_0_header = 12288;
int16_t LUT[3][4096] = { 0 };
bool alc = false;
bool tridiff = false;
//-----------------------------------------------------------------------------
// Subroutines
//-----------------------------------------------------------------------------

// Initialize Hardware
void initHw()
{  // Configure HW to work with 16 MHz XTAL, PLL enabled, system clock of 40 MHz
    SYSCTL_RCC_R = SYSCTL_RCC_XTAL_16MHZ | SYSCTL_RCC_OSCSRC_MAIN
            | SYSCTL_RCC_USESYSDIV | (4 << SYSCTL_RCC_SYSDIV_S);

    // Set GPIO ports to use APB (not needed since default configuration -- for clarity)
    // Note UART on port A must use APB
    SYSCTL_GPIOHBCTL_R = 0;

    //enable clk on timer 1
    SYSCTL_RCGCTIMER_R |= SYSCTL_RCGCTIMER_R1;

    // Enable GPIO port A and F peripherals
    SYSCTL_RCGCADC_R |= SYSCTL_RCGCADC_R0;

    SYSCTL_RCGC2_R = SYSCTL_RCGC2_GPIOA | SYSCTL_RCGC2_GPIOF
            | SYSCTL_RCGC2_GPIOE | SYSCTL_RCGC2_GPIOB;

    // Configure LED pins
    GPIO_PORTF_DIR_R = GREEN_LED_MASK | RED_LED_MASK; // bits 1 and 3 are outputs
    GPIO_PORTF_DR2R_R = GREEN_LED_MASK | RED_LED_MASK; // set drive strength to 2mA (not needed since default configuration -- for clarity)
    GPIO_PORTF_DEN_R = GREEN_LED_MASK | RED_LED_MASK;  // enable LEDs

    // Configure UART0 pins
    GPIO_PORTA_DIR_R |= 2; // enable output on UART0 TX pin: default, added for clarity
    GPIO_PORTA_DEN_R |= 3; // enable digital on UART0 pins: default, added for clarity
    GPIO_PORTA_AFSEL_R |= 3; // use peripheral to drive PA0, PA1: default, added for clarity
    GPIO_PORTA_PCTL_R &= 0xFFFFFF00;       // set fields for PA0 and PA1 to zero
    GPIO_PORTA_PCTL_R |= GPIO_PCTL_PA1_U0TX | GPIO_PCTL_PA0_U0RX;
    // select UART0 to drive pins PA0 and PA1: default, added for clarity

    // Configure UART0 to 115200 baud, 8N1 format
    SYSCTL_RCGCUART_R |= SYSCTL_RCGCUART_R0; // turn-on UART0, leave other UARTs in same status
    delay4Cycles();
    // wait 4 clock cycles
    UART0_CTL_R = 0;                 // turn-off UART0 to allow safe programming
    UART0_CC_R = UART_CC_CS_SYSCLK;                 // use system clock (40 MHz)
    UART0_IBRD_R = 21; // r = 40 MHz / (Nx115.2kHz), set floor(r)=21, where N=16
    UART0_FBRD_R = 45;                               // round(fract(r)*64)=45
    UART0_LCRH_R = UART_LCRH_WLEN_8 | UART_LCRH_FEN; // configure for 8N1 w/ 16-level FIFO
    UART0_CTL_R = UART_CTL_TXE | UART_CTL_RXE | UART_CTL_UARTEN;
    // enable TX, RX, and module

    //configure AINO and AIN1
    GPIO_PORTE_AFSEL_R |= AIN1_MASK | AIN0_MASK; // select alternative functions for AN10 (PE23)
    GPIO_PORTE_DEN_R &= ~(AIN1_MASK | AIN0_MASK); // turn off digital operation on pin PE23
    GPIO_PORTE_AMSEL_R |= AIN1_MASK | AIN0_MASK; // turn on analog operation on pin PE23

    // Configure ADC
    ADC0_CC_R = ADC_CC_CS_SYSPLL; // select PLL as the time base (not needed, since default value)
    ADC0_ACTSS_R &= ~ADC_ACTSS_ASEN3; // disable sample sequencer 3 (SS3) for programming
    ADC0_EMUX_R = ADC_EMUX_EM3_PROCESSOR; // select SS3 bit in ADCPSSI as trigger
    ADC0_SSCTL3_R = ADC_SSCTL3_END0;             // mark first sample as the end
    ADC0_ACTSS_R |= ADC_ACTSS_ASEN3;                 // enable SS3 for operation

    //SSI configuration
    SYSCTL_RCGCSSI_R = SYSCTL_RCGCSSI_R2;            // turn-on SSI2 clocking

    // Configure ~CS for DAC
    GPIO_PORTF_DIR_R |= LDAC_NOT_MASK;  // make bits 1 and 6 outputs PB1 and PB6
    GPIO_PORTF_DR2R_R |= LDAC_NOT_MASK;      // set drive strength to 2mA
    GPIO_PORTF_DEN_R |= LDAC_NOT_MASK;       // enable bits 1 and 6 for digital

    // Configure SSI2 pins for SPI configuration
    GPIO_PORTB_DIR_R |= 0xB0; // make bits pb4(ssi2clk) and pb7(ssi2tx) outputs pb5(ssi2fss)
    GPIO_PORTB_DR2R_R |= 0xB0;                      // set drive strength to 2mA
    GPIO_PORTB_AFSEL_R |= 0xB0; // select alternative functions for MOSI, SCLK pins
    GPIO_PORTB_PCTL_R = GPIO_PCTL_PB7_SSI2TX | GPIO_PCTL_PB4_SSI2CLK
            | GPIO_PCTL_PB5_SSI2FSS; // map alt fns to SSI2
    GPIO_PORTB_DEN_R |= 0xB0;        // enable digital operation on TX, CLK pins
    GPIO_PORTB_PUR_R |= 0x30;                      // must be enabled when SPO=1

    // Configure the SSI2 as a SPI master, mode 3, 16bit operation, 1 MHz bit rate
    SSI2_CR1_R &= ~SSI_CR1_SSE;       // turn off SSI2 to allow re-configuration
    SSI2_CR1_R = 0;                                  // select master mode
    SSI2_CC_R = 0;                    // select system clock as the clock source
    SSI2_CPSR_R = 10;                  // set bit rate to 4 MHz (if SR=0 in CR0)
    SSI2_CR0_R = SSI_CR0_FRF_MOTO | SSI_CR0_DSS_16; // set SR=0, mode 3 (SPH=1, SPO=1), 16-bit
    SSI2_CR1_R |= SSI_CR1_SSE;                       // turn on SSI2

    LDAC_NOT = 1;

    // Configure Timer 1 as the time base
    TIMER1_CTL_R &= ~TIMER_CTL_TAEN;      // turn-off timer before reconfiguring
    TIMER1_CFG_R = TIMER_CFG_32_BIT_TIMER;    // configure as 32-bit timer (A+B)
    TIMER1_TAMR_R = TIMER_TAMR_TAMR_PERIOD; // configure for periodic mode (count down)
    TIMER1_TAILR_R = 400;      // set load value to 40e6 for 1 Hz interrupt rate
    TIMER1_IMR_R = TIMER_IMR_TATOIM;                 // turn-on interrupts
    NVIC_EN0_R |= 1 << (INT_TIMER1A - 16);     // turn-on interrupt 37 (TIMER1A)
    TIMER1_CTL_R |= TIMER_CTL_TAEN;                  // turn-on timer

}

// Blocking function that writes a serial character when the UART buffer is not full
void putcUart0(char c)
{
    while (UART0_FR_R & UART_FR_TXFF)
        ;               // wait if uart0 tx fifo full
    UART0_DR_R = c;                                  // write character to fifo
}

// Blocking function that writes a string when the UART buffer is not full
void putsUart0(char* str)
{
    uint8_t i;
    for (i = 0; i < strlen(str); i++)
        putcUart0(str[i]);
}

// Blocking function that returns with serial data once the buffer is not empty
char getcUart0()
{
    while (UART0_FR_R & UART_FR_RXFE)
        ;               // wait if uart0 rx fifo empty
    return UART0_DR_R & 0xFF;                        // get character from fifo
}

// Request and read one sample from SS3
int16_t readAdc0Ss3()
{
    ADC0_PSSI_R |= ADC_PSSI_SS3;                     // set start bit
    while (ADC0_ACTSS_R & ADC_ACTSS_BUSY)
        ;           // wait until SS3 is not busy
    return ADC0_SSFIFO3_R;                    // get single result from the FIFO
}

void checkInputVoltage()
{
    int16_t raw = 0;
    float instantVolt = 0;
    channel = atoi(param_array[1]);

    if (channel == 1)
    {
        ADC0_SSMUX3_R = 1;                           // set first sample to AIN1

    }
    else if (channel == 0)
    {
        ADC0_SSMUX3_R = 0;                           // set first sample to AIN0
    }
    else
    {
        putsUart0("\r \nincorrect AIN given\r\n");
    }

    putsUart0("checking voltage at  ");
    putsUart0(param_array[1]);
    raw = readAdc0Ss3();

    instantVolt = 3.3 * (raw + 0.5) / 4096.0;

    sprintf(str, "\r\n Raw ADC:%4u\r\n", raw);
    putsUart0(str);
    sprintf(str, "input voltage =%4.1f\r\n", instantVolt);
    putsUart0(str);

}

void clrPositionArray()
{
    uint8_t iter;
    for (iter = 0; iter < 6; iter++)
    {
        position[iter] = 0;
    }
}

void clrParameterArray()
{
    uint8_t i;
    for (i = 0; i < max_Arg; i++)
        *param_array[i] = '\0';

}
//get input string

void getsUart0()
{
    arg_count = 0;
    clrPositionArray();
    clrParameterArray();
    uint8_t cnt = 0;
    uint8_t c;
    L: c = getcUart0();
    putcUart0(c);
    if ((c == 0x7F) && (cnt == 0)) // Checking for backspace and if it is the first entry.
        goto L;
    else if ((c == 0x7F) && (cnt > 0))
    {
        cnt--;
        goto L;
    }
    else
    {
        if (c == 0x0D) // pressing enter detect
        {
            input[cnt] = '\0';
            return;
        }
        else
        {
            if (c < 0x20)  //see if character is printable
                goto L;
            else
            {
                input[cnt++] = tolower(c); // All entries to the input buffer are converted to lowercase
                if (cnt == Max_letter)     // Checking if buffer is full.
                {
                    putsUart0("\r \n Buffer Max Reached \r\n");
                    return;
                }
                else
                    goto L;
            }
        }
    }
}

//character check numeric, alphanumberic

//remove delimiters space and commas from input str
void getposition()
{

    uint8_t i = 0;
    uint8_t j = 0;
    uint8_t k = 0;

//  temp_param[i]= input[i];
    while (input[i] != '\0')
    {

        //spacebar and comma check
        if (input[i] == ' ' || input[i] == ',')
        {
            //  input[i]='\0';
            i++;

        }
        if (input[i] == 8)
        {
            i--;
        }
        else
        {
            //save position in position array
            position[j] = i;
            k = 0;

            while ((input[i] != ' ' || input[i] != ','))
            {
                //get parameter other than space and comma and set in temp_param
                temp_param[k] = input[i];
                if (input[i] == 8)
                {
                    i--;
                }
                if (input[i] == '\0' || (input[i] == ' ' || input[i] == ','))
                {
                    temp_param[k] = '\0';
                    //copy the value in parameter array
                    strcpy(param_array[arg_count], temp_param);

                    break;
                }
                k++;
                i++;

            }
            j++;
            arg_count++;
        }
    }     //end while

}
void waitMicrosecond(uint32_t us)
{
    __asm("WMS_LOOP0:   MOV  R1, #6");
    // 1
    __asm("WMS_LOOP1:   SUB  R1, #1");
    // 6
    __asm("             CBZ  R1, WMS_DONE1");
    // 5+1*3
    __asm("             NOP");
    // 5
    __asm("             NOP");
    // 5
    __asm("             B    WMS_LOOP1");
    // 5*2 (speculative, so P=1)
    __asm("WMS_DONE1:   SUB  R0, #1");
    // 1
    __asm("             CBZ  R0, WMS_DONE0");
    // 1
    __asm("             NOP");
    // 1
    __asm("             B    WMS_LOOP0");
    // 1*2 (speculative, so P=1)
    __asm("WMS_DONE0:");
    // ---
    // 40 clocks/us + error
}

void sysReset()
{
    putsUart0("\r\n Restarting system... \r\n");
    waitMicrosecond(2000000);
    NVIC_APINT_R = 0x04 | (0x05FA << 16);

}

void sendDataSSI(uint16_t data)
{
    LDAC_NOT = 1;
    SSI2_DR_R = data;

    LDAC_NOT = 0;
    __asm(" NOP");
    LDAC_NOT = 1;

    // while (SSI2_SR_R & SSI_SR_BSY);
}

uint16_t computeDc(float input, uint8_t channel)
{
    float val = 0;
    if (channel == 0)
    {
        val = channel_0_slope * input + channel_0_intercept + channel_0_header;
        //  putsUart0("Channel zero selected \r\n");
    }
    else if (channel == 1)
    {
        val = channel_0_slope * input + channel_1_intercept + channel_1_header;
        //  putsUart0("Channel one selected \r\n");
    }
    else
    {
        putsUart0("\r\n Wrong CHannel \r\n");
    }

    return val;

}

void executeAndRunDc()
{
    putsUart0("\r\n Executing DC Commmand \r\n");
    //TODO: checkParameters();

    channel = atoi(param_array[1]);
    dcValue = atof(param_array[2]);
    if (!alc)
    {
        DC[channel] = computeDc(dcValue, channel);
    }
    if (alc)
    {

        DC[channel] = computeDc(errorRaw[channel] * dcValue, channel);

    }
    if (channel == 0)
    {
        channel0[1] = true;
    }
    if (channel == 1)
    {
        channel1[1] = true;
    }
    //  sendDataSSI(raw);

}                                                //run dc command

void setchannelWave(uint8_t channel)
{
    if (channel == 0)
    {
        channel0[1] = false;
    }
    if (channel == 1)
    {
        channel1[1] = false;
    }
}

void setDelPhi(uint8_t channel, float freq)
{
    if (channel == 0)
    {
        ch0Freq = freq;
        deltaphi = freq * pow(2, 32) / 100000;

    }
    else if (channel == 1)
    {
        deltaphi1 = freq * pow(2, 32) / 100000;
        ch1Freq = freq;
    }
}

void setCycleCountInChannel(uint8_t count, uint8_t channel)
{

    if (channel == 0)
    {
        ch0Cycle = count * 100000 / ch0Freq;
        channel0[2] = true;

    }
    else if (channel == 1)
    {
        ch1Cycle = count * 100000 / ch1Freq;
        channel1[2] = true;

    }

}                                                //end set count in channel

bool checkcyclenumeral(char paramArray[])
{
    bool op = false;
    uint8_t y = atoi(paramArray);
    if (!strcmp(paramArray, "continuous"))
    {
        op = false;

    }
    else
    {
        if (y != 0)
        {
            op = true;
        }
    }
    return op;
}                                                // end check numeral

void executeAndRunCycles()
{
    putsUart0("\r\n Computing cycles \r\n");
    uint16_t cycleCount = 0;
    bool isCountProper;
    channel = atoi(param_array[1]);
    isCountProper = checkcyclenumeral(param_array[2]);
    if (isCountProper)
    {
        cycleCount = atoi(param_array[2]);

        setCycleCountInChannel(cycleCount, channel);
    }
    else
    {
        putsUart0("\r\n Continous cycle selected or Improper cycle count\r\n");
        if (channel == 0)
        {
            channel0[2] = false;
        }
        if (channel == 1)
        {
            channel1[2] = false;
        }
    }

}                                                //end cycles function

void executeAndRunSine()
{

    putsUart0("\r\n Computing Sine wave \r\n");

    uint16_t index = 0;
    channel = atoi(param_array[1]);
    dcValue = atof(param_array[2]);
    freq = atof(param_array[3]);
    offset = atof(param_array[4]);
    // raw = computeDc(dcValue, channel);

    setchannelWave(channel);
    setDelPhi(channel, freq);

    for (index = 0; index < 4096; index++)
    {
        if (!alc)
        {
            iVolt = (dcValue * sin(2 * pi * index / 4096)) + offset;
        }
        if (alc)
        {
            iVolt = (errorRaw[channel] * dcValue * sin(2 * pi * index / 4096))
                    + offset;
            //DC[channel]= computeDc(errorRaw[channel]*dcValue, channel);
        }
        LUT[channel][index] = computeDc(iVolt, channel);

    }

}                                                //end sine function

void executeAndRunSquare()
{
    putsUart0("\r\n computing square wave \r\n");
    uint16_t index = 0;
    uint16_t changeIndex = 0;
    channel = atoi(param_array[1]);
    dcValue = atof(param_array[2]);
    freq = atof(param_array[3]);
    offset = atof(param_array[4]);
    if (*param_array[5] != '\0')
    {
        dutyCycle = atof(param_array[5]);
    }
    else
    {
        dutyCycle = 50;
    }
    changeIndex = 4096 * dutyCycle / 100;

    //deltaphi = freq*pow(2, 32)/100000 ;
    setchannelWave(channel);
    setDelPhi(channel, freq);

    for (index = 0; index < changeIndex; index++)
    {
        if (!alc)
        {
            iVolt = (dcValue) + offset;
        }
        if (alc)
        {
            iVolt = errorRaw[channel] * (dcValue) + offset;
            //DC[channel]= computeDc(errorRaw[channel]*dcValue, channel);
        }
        LUT[channel][index] = computeDc(iVolt, channel);
    }
    for (index = changeIndex; index < 4096; index++)
    {
        iVolt = offset;
        LUT[channel][index] = computeDc(iVolt, channel);

    }

}                                                //end square function

void executeAndRunSawtooth()
{
    putsUart0("\r\n computing sawtooth wave \r\n");
    uint16_t index = 0;
    channel = atoi(param_array[1]);
    dcValue = atof(param_array[2]);
    freq = atof(param_array[3]);
    offset = atof(param_array[4]);
    // raw = computeDc(dcValue, channel);
    setchannelWave(channel);
    setDelPhi(channel, freq);

    for (index = 0; index < 4096; index++)
    {
        if (!alc)
        {
            iVolt = (dcValue * index / 2048) - dcValue + offset;
        }
        if (alc)
        {
            iVolt = (errorRaw[channel] * dcValue * index / 2048)
                    - errorRaw[channel] * dcValue + offset;
        }
        LUT[channel][index] = computeDc(iVolt, channel);

    }

}                                                //end function

void executeAndRunHilbert()
{
    putsUart0("\r\n computing second LUT \r\n");
    uint16_t index = 0;
    if (!strcmp(param_array[1], "on"))
    {
        hibdiff = true;

        freq = ch0Freq;
        deltaphi = freq * pow(2, 32) / 100000;

        // raw = computeDc(dcValue, channel);

        for (index = 0; index < 3072; index++)
        {

            LUT[2][index] = 45056 - 12288 + LUT[0][3072 - index];
        }
        for (index = 0; index < 1024; index++)
        {
            LUT[2][3072 + index] = 45056 - 12288 + LUT[0][2048 + index];
        }

    }
    else
    {
        hibdiff = false;
    }
}                                                //end hilbert function

void executeAndRunDifferential()
{
    putsUart0("\r\n computing second LUT \r\n");
    uint16_t index = 0;
    if (!strcmp(param_array[1], "on"))
    {

        hibdiff = true;
        freq = ch0Freq;
        deltaphi = freq * pow(2, 32) / 100000;

        if (!tridiff)
        {

            for (index = 0; index < 4096; index++)
            {
                LUT[2][index] = 45056 - 12288 + LUT[0][4096 - index];
            }
        }
        if (tridiff)
        {
            for (index = 0; index < 2048; index++)
            {
                iVolt = (-dcValue * index / 1024) + dcValue + offset;
                LUT[2][index] = computeDc(iVolt, 1);
            }
            for (index = 2048; index < 4096; index++)
            {
                iVolt = (dcValue * index / 1024) - (3 * dcValue) + offset;
                LUT[2][index] = computeDc(iVolt, 1);
            }

        }

    }
    else
    {
        hibdiff = false;
        tridiff = false;
    }
}                                                //end differntial function

void calculateGain()
{
    putsUart0("\r\n Gain calculation mode on \r\n");
    uint16_t index = 0;
    float freq1, freq2, Vin1, Vin2, gain, step = 0;
    freq1 = atof(param_array[1]);
    freq2 = atof(param_array[2]);
    step = atof(param_array[3]);
    int16_t raw = 0;
    channel0[1] = false;  //wave
    channel0[0] = true;     //run ch0
    putsUart0("\r\n Freq \t  Vin1 \t Vin2 \t Gain \r\n");
    deltaphi = freq * pow(2, 32) / 100000;
    for (index = 0; index < 4096; index++)
    {
        iVolt = 4 * (sin(2 * pi * index / 4096));
        LUT[0][index] = computeDc(iVolt, 0);
    }

    for (freq = freq1; freq < freq2; freq = freq + step)
    {
        deltaphi = freq * pow(2, 32) / 100000;
        waitMicrosecond(2000000);

        ADC0_SSMUX3_R = 1;                           // set first sample to AIN1
        raw = readAdc0Ss3();
        Vin1 = 3.3 * (raw + 0.5) / 4096.0;
        delay4Cycles();
        ADC0_SSMUX3_R = 0;                           // set first sample to AIN0
        raw = readAdc0Ss3();
        Vin2 = 3.3 * (raw + 0.5) / 4096.0;

        gain = (Vin1 / Vin2);

        sprintf(str, "\r\n  %4.1f \t %4.1f \t %4.1f \t %4.3f \r\n", freq, Vin1,
                Vin2, gain);
        putsUart0(str);

    }
////                sprintf(str, "\r\n Raw ADC:%4u\r\n", raw);
////                       putsUart0(str);
////                       sprintf(str, "input voltage =%4.1f\r\n", instantVolt);
////                       putsUart0(str);
//
//
//
//

}                               //end gain function

void alcErrorCompute()
{
    //alc check channel voltage
    int16_t raw = 0;
    float voltin, voltage = 0;
    channel = atoi(param_array[2]);
    voltage = atof(param_array[3]);
    if (!strcmp(param_array[1], "check"))
    {

        DC[channel] = computeDc(voltage, channel);

        ADC0_SSMUX3_R = 0;                           // set first sample to AIN0

        if (channel == 1)
        {
            channel1[0] = true;
            channel1[1] = true;

        }
        if (channel == 0)
        {
            channel0[0] = true;
            channel0[1] = true;

        }
        waitMicrosecond(1000000);
        raw = readAdc0Ss3();
        voltin = 3.3 * (raw + 0.5) / 4096.0;
        sprintf(str, "\r\n Raw ADC:%4u\r\n", raw);
        putsUart0(str);
        sprintf(str, "ALC check voltage =%4.1f\r\n", voltin);
        putsUart0(str);

        if (voltin < voltage)
        {
            errorRaw[channel] = (voltage / voltin);
            //errorRaw[channel] = computeDc(error, channel);

        }
    }
    if (!strcmp(param_array[1], "on"))
    {
        putsUart0("\r\n ALC mode on \r\n");
        alc = true;
    }
    if (!strcmp(param_array[1], "off"))
    {
        alc = false;
    }
    channel0[0] = false;
    channel0[1] = false;
    channel0[0] = true;
    channel0[1] = true;

}

void executeAndRunTriangle()
{
    putsUart0("\r\n computing Triangle LUT \r\n");
    uint16_t index = 0;
    tridiff = true;
    channel = atoi(param_array[1]);
    dcValue = atof(param_array[2]);
    freq = atof(param_array[3]);
    offset = atof(param_array[4]);
    // raw = computeDc(dcValue, channel);
    setchannelWave(channel);
    setDelPhi(channel, freq);

    for (index = 0; index < 2048; index++)
    {
        if (!alc)
        {
            iVolt = (dcValue * index / 1024) - dcValue + offset;
        }
        if (alc)
        {
            iVolt = (errorRaw[channel] * dcValue * index / 1024)
                    - errorRaw[channel] * dcValue + offset;
        }
        LUT[channel][index] = computeDc(iVolt, channel);
    }
    for (index = 2048; index < 4096; index++)
    {
        if (!alc)
        {
            iVolt = (-dcValue * index / 1024) + (3 * dcValue) + offset;
        }
        if (alc)
        {
            iVolt = (-errorRaw[channel] * dcValue * index / 1024)
                    + (3 * errorRaw[channel] * dcValue) + offset;
        }
        LUT[channel][index] = computeDc(iVolt, channel);
    }

}                               //end triangle function

/*Mux table for channel 0 and 1 for dc,wave and stop/run
 bit 0 (run/~stop)      bit 1(dc/~wave)
 channelx[i]                  0                     x       stop
 1                     1       run dc
 1                     0       run wave
 */

void executeAndRunWaveform()
{
    putsUart0("\r\n Run all waveforms \r\n");
    channel0[0] = true; // run bit high
    channel1[0] = true;

}

void executeAndStopWaveform()
{
    putsUart0("\r\n Stop all waveforms \r\n");
    channel0[0] = false;
    channel1[0] = false; // run but low

}

void sendZeroSSI(uint8_t channel)
{
    if (channel == 0)
    {
        sendDataSSI(channel_0_intercept + channel_0_header);
    }
    if (channel == 1)
    {
        sendDataSSI(channel_1_intercept + channel_1_header);
    }
} //end send Zero SSI

void timer1ISR()
{
    if (channel0[0] && hibdiff)
    { // differential or hilbert mode op
        phi = phi + deltaphi;
        // send LUT value of wave to channel 1
        sendDataSSI(LUT[0][phi >> 20]);
        sendDataSSI(LUT[2][phi >> 20]);

    }

    if (channel0[0] && !hibdiff)
    {                        //isRun
        if (!channel0[1] && !channel0[2])
        {                    // isWave and ! cycle mode
            phi = phi + deltaphi;
            //send LUT value of wave to channel 0
            sendDataSSI(LUT[0][phi >> 20]);
        }
        else if (channel0[1])
        {            //isDC
            sendDataSSI(DC[0]);
        }

    }
    if (channel1[0] && !hibdiff)
    {
        if (!channel1[1] && !channel1[2])
        {                    // isWave and not cycle mode
            phi1 = phi1 + deltaphi1;
            // send LUT value of wave to channel 1
            sendDataSSI(LUT[1][phi1 >> 20]);
        }
        else if (channel1[1])
        {            //isDC

            sendDataSSI(DC[1]);

        }
    }
    if (!channel0[0] && !channel0[0])
    {
        //send absolute zero data to both channels
        sendZeroSSI(0);
        delay4Cycles();
        sendZeroSSI(1);

    }
    if (channel0[2] && channel0[0])
    {            // for cycles
        if (ch0Cycle != 0)
        {
            phi = phi + deltaphi;
            //send LUT value of wave to channel 0
            sendDataSSI(LUT[0][phi >> 20]);
            ch0Cycle--;
        }
        else
            sendZeroSSI(0);
    }
    if (channel1[2] && channel1[0])
    { // for cycles ch 1
        if (ch1Cycle != 0)
        {
            phi1 = phi1 + deltaphi1;
            //send LUT value of wave to channel 0
            sendDataSSI(LUT[1][phi1 >> 20]);
            ch1Cycle--;
        }
        else
            sendZeroSSI(1);
    }

    TIMER1_ICR_R = TIMER_ICR_TATOCINT;               // clear interrupt flag

}               //end TImer1 ISR

//check command
void checkCommand(void)
{
    if (!strcmp(param_array[0], "reset"))
    {
        sysReset();
    }
    else if (!strcmp(param_array[0], "dc"))
    {
        executeAndRunDc();
    }
    else if (!strcmp(param_array[0], "cycles"))
    {
        executeAndRunCycles();
    }
    else if (!strcmp(param_array[0], "sine"))
    {
        executeAndRunSine();
    }
    else if (!strcmp(param_array[0], "square"))
    {
        executeAndRunSquare();
    }
    else if (!strcmp(param_array[0], "sawtooth"))
    {
        executeAndRunSawtooth();
    }
    else if (!strcmp(param_array[0], "triangle"))
    {
        executeAndRunTriangle();
    }
    else if (!strcmp(param_array[0], "run"))
    {
        executeAndRunWaveform();
    }
    else if (!strcmp(param_array[0], "stop"))
    {
        executeAndStopWaveform();
    }
    else if (!strcmp(param_array[0], "voltage"))
    {
        checkInputVoltage();
    }
    else if (!strcmp(param_array[0], "hilbert"))
    {
        executeAndRunHilbert();
    }
    else if (!strcmp(param_array[0], "differential"))
    {
        executeAndRunDifferential();
    }
    else if (!strcmp(param_array[0], "alc"))
    {
        alcErrorCompute();
    }
    else if (!strcmp(param_array[0], "gain"))
    {
        calculateGain();
    }

    else
    {
        putsUart0("\r \n Error: Command not recognized \r\n");
    }

}               // end check command

void init_interface()
{
    getsUart0();
    getposition();
    checkCommand();

}
//-----------------------------------------------------------------------------
// Main
//-----------------------------------------------------------------------------

int main(void)
{
    // Initialize hardware
    initHw();

    // Display greeting
    putsUart0("\r\n Serial Example \r\n");

    putcUart0('>');

    while (1)
    {
        init_interface();

        //     timer1ISR();

    }               //end while

}               //end main

