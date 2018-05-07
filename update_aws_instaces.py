import boto3
import paramiko
ec2 = boto3.client('ec2')
dnss = map(lambda y: y['Instances'][0]['PublicDnsName'], filter(lambda x: x['Instances'][0]['Tags'][0]['Value'].startswith('omer'), ec2.describe_instances()['Reservations']))
for dns in dnss:
	client = paramiko.SSHClient()
	client.set_missing_host_key_policy(paramiko.AutoAddPolicy)
	client.connect(dns, username='ubuntu', key_filename='omer1.pem')
	sin, sout, serr = client.exec_command('cd Codenator; git pull; chmod +x *.sh')
	sout.channel.recv_exit_status()
	client.close()