A web service that manages running instances of Kind on problem submitted by users. Similar to http://rise4fun.com/dev. The web service returns XML data.

# Protocol

## `/submitjob (POST)`


The user submits a file and parameters for Kind. Return an XML string containing the ID of the created job.

### Parameters

| Name | Format |
---------------
| file	| Lustre file |
| kind	| `kind2` to run Kind 2, `pkind` to run Kind 1, `jkind` to run JKind |
| arg	| Command line argument (the argv array), may be repeated, must be in the correct order |
--------------------
### Response

createjob: Successful
<jobstatus msg="started" jobid="ID">
Job started with ID XYZ
</jobstatus>
createjob: Rejected
<jobstatus msg="rejected">
Job rejected due to high system load.
</jobstatus>
retrievejob/<ID> (GET)

The user queries the job with the given ID, which is part of the request URL. Return an XML string containing the output of the given job since the last retrieve.
Parameters

None, job ID is part of the request URI
Response
retrievejob: Job completed
<jobstatus msg="completed">
Job with ID XYZ has completed and was retrieved at 2014-03-01 12:00 UTC
</jobstatus>
retrievejob: Job is running
<jobstatus msg="running">
output
</jobstatus>
retrievejob: Job aborted
<jobstatus msg="aborted">
Job with ID XYZ aborted before completion.
Contents of stderr:
%s
</jobstatus>
retrievejob: Job not found
<jobstatus msg="notfound">
Job with ID XYZ not found.
</jobstatus>
/canceljob/ID (GET)

The user requests to cancel the job with the given ID, which is part of the request URL. Return an XML string indicating success.
Parameters

None, job ID is part of the request URI
Response
retrievejob: Job not found
<jobstatus msg="inprogress">
Requested canceling of job with ID XYZ.
</jobstatus>
canceljob: Job not found
<jobstatus msg="notfound">
Job with ID XYZ not found.
</jobstatus>
