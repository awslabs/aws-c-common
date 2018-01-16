## AWS C Common

Core c99 package for AWS SDK for C. Includes cross-platform primitives, configuration, data structures, and error handling.

## License

This library is licensed under the Apache 2.0 License. 

## Error Codes
The error handling infrastructure is designed to support multiple libraries. For this to work, AWS maintained libraries 
have pre-slotted error codes for each library. The currently allocated error ranges are:

| Range | Library Name |
| --- | --- |
| [0, 0x0400) | aws-c-common |
| [0x0400, 0x0800) | aws-c-io |
| [0x0800, 0x1000) | aws-c-http |
| [0x1000, 0x2000) |aws-c-amazon-flow | 

Each library should begin its error codes at the beginning of its range and follow in sequence (don't skip codes).
